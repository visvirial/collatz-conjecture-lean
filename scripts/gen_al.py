#!/usr/bin/env python3
"""Generate the Lean modules of a kernel-run Applegate-Lagarias check (Collatz/LongStopAL.lean).

Input: the prefix tree printed by `TREE="W0 mmax" ./al_vec P Q D split Lmax Tbig 1`
(scripts/al_vec.c), optionally xz-compressed:
    S <r> <m>                       the class r mod 3^m is split into its three children
    L <r> <m> <ok> <work> <T_1>,... a leaf: chunk theorem with per-level bands T_w

Output (under OUT/ALGen/<tag>/, module prefix ALGen.<tag>):
    K<i>.lean  "chunk modules" (no Mathlib): for a run of consecutive subtrees (in DFS order) whose
               total kernel work is at most BUDGET steps, one `decide +kernel` theorem per leaf.
    A<i>.lean  "assembly modules": `chunk_sound'` turns each leaf into `Covered P Q r (3^m)` and
               `covered_split` combines the inner nodes, one module per subtree of at most FANIN
               imported modules.
    Final.lean `long_stopping_AL_<P>_<Q>` and its axiom audit.
    modules.txt  one line per module: `<name> <estimated kernel steps> <imports...>` in dependency
               order (all K modules first), for the CI shards and the assembly.

The generation is deterministic. Hints only steer the kernel search: a wrong hint makes a
`decide +kernel` fail, never succeed (Collatz.LSA.chunk_sound holds for all hints).

usage: gen_al.py TREE P Q OUT TAG [BUDGET] [FANIN]
"""
import lzma
import os
import sys

F = 64  # chain fuel, as in Collatz/LongStopAL.lean


def read_tree(path):
    op = lzma.open if path.endswith(".xz") else open
    S, L = set(), {}
    with op(path, "rt") as f:
        for line in f:
            if line.startswith("S "):
                _, r, m = line.split()
                S.add((int(r), int(m)))
            elif line.startswith("L "):
                t = line.split()
                r, m, ok, work = int(t[1]), int(t[2]), int(t[3]), int(t[4])
                if ok != 1:
                    sys.exit(f"leaf {r} {m} failed in the C mirror")
                ts = [int(x) for x in t[5].strip(",").split(",")]
                while len(ts) > 1 and ts[-1] == 0 and ts[-2] == 0:
                    ts.pop()
                L[(r, m)] = (work, ts)
            elif line.startswith("# done") and " fail=0 " not in line:
                sys.exit("the tree run reported failures: " + line.strip())
    return S, L


def main():
    tree, P, Q, out, tag = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
    budget = int(sys.argv[6]) if len(sys.argv) > 6 else 2_000_000
    fanin = int(sys.argv[7]) if len(sys.argv) > 7 else 1000
    S, L = read_tree(tree)
    P3 = [3 ** i for i in range(64)]

    def children(r, m):
        return [(r + j * P3[m], m + 1) for j in range(3)]

    # check that the tree is a complete ternary prefix tree over the roots 1, 2 mod 3
    work = {}

    def walk(node):  # post-order, iterative
        stack = [(node, False)]
        while stack:
            v, done = stack.pop()
            if v in L:
                work[v] = L[v][0] + 1
                continue
            if v not in S:
                sys.exit(f"class {v} is neither split nor a leaf")
            if done:
                work[v] = sum(work[c] for c in children(*v))
            else:
                stack.append((v, True))
                stack.extend((c, False) for c in reversed(children(*v)))

    roots = [(1, 1), (2, 1)]
    for v in roots:
        walk(v)
    if len(work) != len(S) + len(L):
        sys.exit("the tree has classes outside the subtrees of 1 and 2 mod 3")

    # maximal subtrees with work <= budget, in DFS order; inner nodes above them
    blocks, inner = [], []

    def cut(v):
        if work[v] <= budget or v in L:
            blocks.append(v)
            return
        inner.append(v)
        for c in children(*v):
            cut(c)

    for v in roots:
        cut(v)

    # pack consecutive blocks into chunk modules
    kmods, cur, cw = [], [], 0
    for b in blocks:
        if cur and cw + work[b] > budget:
            kmods.append(cur)
            cur, cw = [], 0
        cur.append(b)
        cw += work[b]
    if cur:
        kmods.append(cur)
    pre = f"ALGen.{tag}"
    d = os.path.join(out, "ALGen", tag)
    os.makedirs(d, exist_ok=True)
    head = ("set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
            "set_option Elab.async false\nset_option linter.all false\n\nnamespace Collatz.LSA\n\n")
    listing = []

    def name(v):
        return f"c_{v[1]}_{v[0]}"

    def digits(r, m):
        ds = []
        for _ in range(m):
            ds.append(r % 3)
            r //= 3
        return ds

    def emit_split(f, v):
        r, m = v
        a, b, c = (name(x) for x in children(r, m))
        f.write(f"theorem {name(v)} : Covered {P} {Q} {r} {P3[m]} :=\n"
                f"  covered_split (P := {P}) (Q := {Q}) (r := {r}) (M := {P3[m]}) {a} {b} {c}\n\n")

    kof = {}  # block root -> chunk module holding its leaves
    for i, mod in enumerate(kmods):
        mn = f"K{i:05d}"
        with open(os.path.join(d, mn + ".lean"), "w") as f:
            f.write("import Collatz.LSA.Basic\n\n" + head)
            for b in mod:
                stack = [b]
                while stack:
                    v = stack.pop()
                    if v in S:
                        stack.extend(reversed(children(*v)))
                        continue
                    r, m = v
                    ds = digits(r, m)
                    js = ",".join(map(str, ds[1:]))
                    ts = ",".join(map(str, L[v][1]))
                    f.write(f"theorem k_{m}_{r} : chunk {P} {Q} {F} {ds[0]} [{js}] [{ts}] = true := by\n"
                            f"  decide +kernel\n")
                kof[b] = f"{pre}.{mn}"
            f.write("end Collatz.LSA\n")
        listing.append((f"{pre}.{mn}", sum(work[b] for b in mod), ["Collatz.LSA.Basic"]))

    def emit_leaf(f, v):
        r, m = v
        ds = digits(r, m)
        f.write(f"theorem {name(v)} : Covered {P} {Q} {r} {P3[m]} :=\n"
                f"  chunk_sound' (Or.{'inl' if ds[0] == 1 else 'inr'} rfl) rfl k_{m}_{r}\n\n")

    # assembly modules: a subtree of the inner nodes above the blocks, together with the blocks
    # below it (leaf conversions and the splits inside the blocks), importing at most `fanin`
    # modules (chunk modules of its blocks, assembly modules of sub-subtrees)
    blockset = set(kof)
    home = {}  # node -> assembly module defining c(node)

    def frontier(v):  # (blocks, already assembled nodes) at the bottom of the region of v
        bl, done, stack = [], [], [v]
        while stack:
            x = stack.pop()
            if x in home:
                done.append(x)
            elif x in blockset:
                bl.append(x)
            else:
                stack.extend(children(*x))
        return bl, done

    amods = []

    def assemble(v):
        if v in home:
            return
        bl, done = frontier(v)
        if len({kof[b] for b in bl}) + len({home[x] for x in done}) > fanin and v not in blockset:
            for c in children(*v):
                assemble(c)
            bl, done = frontier(v)
        mn = f"A{len(amods):05d}"
        imports = sorted({kof[b] for b in bl} | {home[x] for x in done})
        nodes = []  # post-order over the region (children before parents)
        stack = [(v, False)]
        while stack:
            x, exp = stack.pop()
            if x in home:
                continue
            if x in L:
                nodes.append(x)
                continue
            if exp:
                nodes.append(x)
            else:
                stack.append((x, True))
                stack.extend((c, False) for c in reversed(children(*x)))
        with open(os.path.join(d, mn + ".lean"), "w") as f:
            f.write("import Collatz.LongStopAL\n" + "".join(f"import {x}\n" for x in imports) + "\n" + head)
            for x in nodes:
                (emit_leaf if x in L else emit_split)(f, x)
            f.write("end Collatz.LSA\n")
        for x in nodes:
            home[x] = f"{pre}.{mn}"
        amods.append((f"{pre}.{mn}", len(nodes), ["Collatz.LongStopAL"] + imports))

    for v in roots:
        assemble(v)
    listing.extend(amods)
    fin = sorted({home[v] for v in roots})
    with open(os.path.join(d, "Final.lean"), "w") as f:
        f.write("".join(f"import {x}\n" for x in fin))
        f.write(f"""
namespace Collatz.LSA

/-- Infinitely many `n` need `σ(n) ≥ γ log n - c` steps with `γ = {Q}/({Q} log 2 - {P} log 3)`:
the kernel-run Applegate–Lagarias search with ratio `{P}/{Q}` covers all `3`-adic units. -/
theorem long_stopping_AL_{P}_{Q} (N : ℕ) : ∃ n L, N ≤ L ∧ 1 ≤ n ∧ kstepT^[L + 2] n = 1 ∧
    (∀ i < L + 2, kstepT^[i] n ≠ 1) ∧
    ({Q} : ℕ) * Real.log n - 2 * ({P} : ℕ) * Real.log 3 ≤
      (({Q} : ℕ) * Real.log 2 - ({P} : ℕ) * Real.log 3) * (L + 2 : ℕ) :=
  long_stopping_AL (units_of_covered c_1_1 c_1_2) N

end Collatz.LSA

/--
info: 'Collatz.LSA.long_stopping_AL_{P}_{Q}' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Collatz.LSA.long_stopping_AL_{P}_{Q}
""")
    listing.append((f"{pre}.Final", 0, fin))
    with open(os.path.join(d, "modules.txt"), "w") as f:
        for n, w, imps in listing:
            f.write(f"{n} {w} {' '.join(imps)}\n")
    print(f"leaves={len(L)} inner={len(S)} work={work[(1, 1)] + work[(2, 1)]} "
          f"chunk_modules={len(kmods)} assembly_modules={len(amods)}", file=sys.stderr)


if __name__ == "__main__":
    main()
