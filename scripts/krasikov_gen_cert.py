#!/usr/bin/env python3
"""Find the certificate used in Collatz/KrasikovGen.lean.

Usage: krasikov_gen_cert.py H A K U V [ITERS [CHUNK]]

Hypothesis classes are residues mod M = 3^H; a node is known mod 3M, which determines the
residues mod M of its children (2^a m - 1)/3 for 2 <= a <= A.  With c = U/V we look for
C_r >= 0 with

  sum_a C_{child} W_a >= C_{s mod M} 2^K     for every s mod 3M prime to 3,

where W_a are integers with W_a^V 2^(aU) <= 3^U 2^(KV), i.e. W_a / 2^K <= (3/2^a)^c.
The C_r come from the power iteration C <- min_s sum_a C_child (3/2^a)^c (normalized), are
rounded down to 20-bit integers, and the integer inequalities are checked exactly.

Output (stdout): the instance section of the Lean file -- the constants packed into one natural
number `KGC` (21 bits per residue), the weights `KGW`, and the kernel checks in pieces of CHUNK
residues.  The file uses `krasikov_gen_cert.py 9 30 40 303 625 800` (pure Python, about 8 minutes).
"""
import sys
sys.set_int_max_str_digits(0)

H, A, K, U, V = map(int, sys.argv[1:6])
ITERS = int(sys.argv[6]) if len(sys.argv) > 6 else 400
M = 3 ** H
T = 3 * M
c = U / V
CB = 21  # bits per constant
SCALE = 2 ** 20


def kids(s):
    out = []
    for a in range(2, A + 1):
        n = (2 ** a * s) % T
        if n % 9 in (4, 7):
            out.append((a, (n - 1) // 3 % M))
    return out


KIDS = {s: kids(s) for s in range(T) if s % 3}

# integer weights W_a <= 2^K (3/2^a)^c, checked exactly through V-th powers
W = [0] * (A + 1)
for a in range(A + 1):
    w = int(2 ** K * (3 / 2 ** a) ** c) + 1
    while w ** V * 2 ** (a * U) > 3 ** U * 2 ** (K * V):
        w -= 1
    W[a] = w
WB = max(W).bit_length()

# power iteration
wf = [w / 2 ** K for w in W]
C = [1.0 if r % 3 else 0.0 for r in range(M)]
for it in range(ITERS):
    new = [float('inf') if r % 3 else 0.0 for r in range(M)]
    for s, ks in KIDS.items():
        v = sum(wf[a] * C[ch] for a, ch in ks)
        r = s % M
        if v < new[r]:
            new[r] = v
    top = max(new)
    lmin = min(new[r] / C[r] for r in range(M) if r % 3 and C[r] > 0)
    C = [x / top for x in new]
print("lambda_min (float) =", lmin, file=sys.stderr)

Ci = [int(x * (SCALE - 1)) for x in C]
ok = all(sum(Ci[ch] * W[a] for a, ch in ks) >= Ci[s % M] * 2 ** K for s, ks in KIDS.items())
print("exact check:", ok, " C(5) =", Ci[5 % M], file=sys.stderr)
assert ok and Ci[5 % M] > 0 and max(Ci) < 2 ** CB

# the constants packed into one number (CB bits per residue), likewise the weights
BC = sum(x << (CB * r) for r, x in enumerate(Ci))
BW = sum(x << (WB * a) for a, x in enumerate(W))
CHUNK = int(sys.argv[7]) if len(sys.argv) > 7 else 2187
assert T % CHUNK == 0
NP = T // CHUNK
nm = f"kgc{H}"
Cf = f"(kgTab KGC {CB})"
Wf = f"(kgTab KGW {WB})"
out = []
out.append(f"/-! ## The instance mod `3^{H}` -/\n")
out.append(f"/-- The constants on the residues mod `3^{H}` ({CB} bits each). -/")
out.append(f"def KGC : ℕ := {BC}\n")
out.append(f"/-- The weights `W a ≤ 2^{K} (3/2^a)^({U}/{V})` for `a ≤ {A}` ({WB} bits each). -/")
out.append(f"def KGW : ℕ := {BW}\n")
out.append(f"theorem kgw{H} : KGWeights {Wf} {A} {K} {U} {V} := by")
out.append(f"  apply kgWeights_of_kall")
out.append(f"  decide +kernel\n")
out.append("section Pieces")
out.append("")
out.append("/- Checked one after the other: with asynchronous elaboration the kernel's intermediate")
out.append("numbers of all pieces stay alive together (about 10 GB more peak memory). -/")
out.append("set_option Elab.async false")
out.append("")
for j in range(NP):
    out.append(f"theorem {nm}_{j} : kallFrom (kgOk {Cf} {Wf} {M} {A} {K}) {j * CHUNK} {CHUNK} = true := by\n  decide +kernel")
out.append("")
out.append("end Pieces")
expr = f"{nm}_0"
for j in range(1, NP):
    expr = f"(kallFrom_append {expr} {nm}_{j})"
out.append("")
out.append(f"theorem {nm} : KGCert {Cf} {Wf} {M} {A} {K} := by")
out.append(f"  apply kgCert_of_kall")
out.append(f"  have h := {expr}")
out.append(f"  simpa [kallFrom] using h\n")
out.append(f"theorem {nm}_five : 0 < {Cf[1:-1]} (5 % {M}) := by decide +kernel\n")
out.append(f"""open Classical in
/-- **At least `κ N^({U}/{V})` integers `n ≤ N` reach `1`** (`{U}/{V} = {U/V}`), by Krasikov's
method with constants mod `3^{H}`. -/
theorem card_reachesOne_ge_rpow_krasikov :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 5 ≤ N →
      κ * (N : ℝ) ^ (({U} : ℝ) / {V}) ≤ (((range (N + 1)).filter ReachesOne).card : ℝ) := by
  obtain ⟨κ, hκ, h⟩ := card_reachesOne_ge_gen (by norm_num) (by norm_num) (by norm_num) {nm} kgw{H}
    kgc{H}_five
  refine ⟨κ, hκ, fun N hN => ?_⟩
  have := h N hN
  rwa [show (({U} : ℕ) : ℝ) / (({V} : ℕ) : ℝ) = ({U} : ℝ) / {V} by norm_num] at this

end Collatz""")
print("\n".join(out))
