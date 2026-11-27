#!/usr/bin/env python3
"""Parameters of the bounded Steiner theorem (Collatz/Circuit.lean, CollatzBig/Circuit*.lean).

A circuit (k odd T-steps, then l even ones, K = k + l) through n >= N needs
0 < K ln 2 - k ln 3 < ln(1 + 1/N). This script (100-digit decimal logarithms):

* lists the convergents of log2 3 with their gaps K ln 2 - k ln 3 relative to eps = ln(1 + 1/N);
* checks the parameters used in CollatzBig/CircuitCert.lean: the Farey pair
  9809721694/6189245291 < log2 3 < 630138897/397573379 (determinant 1, KBOUND = b + d),
  the anchors R1, R2 for the lower bound, the condition 2^c/3^d >= 1 + 1/(2N), and the
  approximate quotient n = (3^d - 2^d)/(2^c - 3^d) of the only remaining candidate (K, k) = (c, d).

The exact inequalities are certified by the kernel; this script only chooses the numbers.
Usage: python3 scripts/circuit_cert.py [N]   (default N = 7281311744)
"""
import sys
from decimal import Decimal as D, getcontext

getcontext().prec = 100
L2, L3 = D(2).ln(), D(3).ln()
N = int(sys.argv[1]) if len(sys.argv) > 1 else 7281311744
eps = (1 + D(1) / N).ln()

# convergents of log2 3
x, cf = L3 / L2, []
for _ in range(25):
    q = int(x)
    cf.append(q)
    x = 1 / (x - q)
p0, q0, p1, q1 = 1, 0, cf[0], 1
print("convergents K/k, gap = K ln2 - k ln3, gap/eps")
for t in cf[1:]:
    p0, q0, p1, q1 = p1, q1, t * p1 + p0, t * q1 + q0
    g = p1 * L2 - q1 * L3
    print(f"  {p1}/{q1}  gap {float(g):+.4e}  gap/eps {float(g / eps):+.4f}")

a, b = 357638239, 225644606        # lower convergent (anchor)
c, d = 630138897, 397573379        # upper convergent
j = 15
A, B = a + j * c, b + j * d        # lower convergent 9809721694 / 6189245291
assert b * c - a * d == 1 and B * c - A * d == 1 and d < B
print("pair", A, B, c, d, "KBOUND = b + d =", B + d)

g0 = b * L3 - a * L2               # ln(3^b / 2^a)
g1 = c * L2 - d * L3               # ln(2^c / 3^d)
assert g0 > 0 and g1 > 0 and B * L3 - A * L2 > 0
x0 = 1 - (-g0).exp()               # 1 - 2^a/3^b
x1 = g1.exp() - 1                  # 2^c/3^d - 1
R1, R2 = 594045519, 9447912334
assert D(1) / R1 < x0, "R1 * 2^a <= (R1 - 1) * 3^b fails"
assert D(1) / R2 > x1, "R2 * 2^c <= (R2 + 1) * 3^d fails"
assert (R1 - 1) * (R2 + 1) ** j < R1 * R2 ** j
assert x1 > D(1) / (2 * N), "(2N + 1) 3^d <= 2N 2^c fails"
assert 2 * g1 > eps and B * L3 - A * L2 + g1 > eps
n = (1 - (-d * (L3 - L2)).exp()) / x1
print("R1", R1, "1/x0", f"{float(1 / x0):.6f}", " R2", R2, "1/x1", f"{float(1 / x1):.6f}")
print("candidate (K, k) = (c, d): n =", f"{n:.6f}", "(not an integer)")
B20 = 1 << 20
for name, e in [("a", a), ("b", b), ("c", c), ("d", d)]:
    print(f"  {name} = 1048576 * {e // B20} + {e % B20}")
