#!/usr/bin/env python3
"""Generate Lean chunk theorems for the kernel-run Applegate-Lagarias search (Collatz/LSA/Basic.lean).

Input: the `H` lines of `HINTS=1 ./al_vec P Q D split Lmax Tbig sample` (scripts/al_vec.c):
    H <r> <m> ok=<0|1> work=<steps> cw=<codewords> T=<T_1>,<T_2>,...
where r is the class residue mod 3^m and T_w the band for entries of weight w.

Output: one Lean file with `theorem <prefix>_<i> : chunk P Q F r0 js Ts = true := by decide +kernel`
per line (r0 = r % 3, js = the further base-3 digits of r, Ts = [T_1, T_2, ...] with trailing zeros
cut to one). Hints only steer the search: a wrong hint makes `decide` fail, never succeed.

usage: gen_lsa.py P Q hints.txt out.lean [prefix] [max_chunks]
"""
import sys


def digits(r, m):
    ds = []
    for _ in range(m):
        ds.append(r % 3)
        r //= 3
    return ds


def main():
    P, Q = int(sys.argv[1]), int(sys.argv[2])
    src, out = sys.argv[3], sys.argv[4]
    prefix = sys.argv[5] if len(sys.argv) > 5 else "lsa"
    cap = int(sys.argv[6]) if len(sys.argv) > 6 else 10 ** 9
    lines = [l.split() for l in open(src) if l.startswith("H ")][:cap]
    with open(out, "w") as f:
        f.write("import Collatz.LSA.Basic\n\nnamespace Collatz.LSA\n\n")
        f.write("set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n")
        for i, l in enumerate(lines):
            r, m = int(l[1]), int(l[2])
            ts = [int(x) for x in l[6][2:].strip(",").split(",")]
            while len(ts) > 1 and ts[-1] == 0 and ts[-2] == 0:
                ts.pop()
            ds = digits(r, m)
            js = ",".join(map(str, ds[1:]))
            tl = ",".join(map(str, ts))
            f.write(f"-- {l[4]} {l[5]}\n")
            f.write(f"theorem {prefix}_{i} : chunk {P} {Q} 64 {ds[0]} [{js}] [{tl}] = true := by\n"
                    f"  decide +kernel\n\n")
        f.write("end Collatz.LSA\n")


if __name__ == "__main__":
    main()
