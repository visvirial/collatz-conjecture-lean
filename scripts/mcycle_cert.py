#!/usr/bin/env python3
"""Parameters of the bounded Baker-free theorem on m-cycles (Collatz/MCycle.lean,
CollatzBig/MCycleCert.lean, CollatzBig/MCycle.lean).

A T-cycle with m odd blocks, k odd steps and K steps whose elements are all >= N satisfies
3^k < 2^K and N^m 2^K <= (N+1)^m 3^k, i.e. 0 < K ln 2 - k ln 3 <= m ln(1 + 1/N).
For each m the best Farey pair a/b < log2 3 < c/d is the one where the Stern-Brocot descent
stops: the upper fraction still has gap > m ln(1 + 1/N), its mediant with the lower one not.
Then every such cycle has k >= b + d. The certificates are
  2^a < 3^b,  (M+1) 3^d <= M 2^c,  (N+1)^m M < N^m (M+1)  (exact integers),
the first two checked by the kernel, the third by `decide +kernel` (small numbers).

Usage: python3 scripts/mcycle_cert.py [N]   (default N = 7281311744)
"""
import sys
from decimal import Decimal as D, getcontext

getcontext().prec = 100
L2, L3 = D(2).ln(), D(3).ln()
TH = L3 / L2
N = int(sys.argv[1]) if len(sys.argv) > 1 else 7281311744
EPS = (1 + D(1) / N).ln()


def best(m):
    a, b, c, d = 1, 1, 2, 1
    while True:
        p, q = a + c, b + d
        if p / D(q) > TH:
            if p * L2 - q * L3 > m * EPS:
                c, d = p, q
            else:
                return a, b, c, d
        else:
            a, b = p, q


def M_of(c, d):
    x1 = (c * L2 - d * L3).exp() - 1          # 2^c / 3^d - 1
    M = int(1 / x1) + 1
    assert D(1) / M <= x1                      # (M+1) 3^d <= M 2^c
    return M


rows, prev = [], None
for m in range(1, 2000):
    pair = best(m)
    if prev is not None and pair != prev[1]:
        rows.append((prev[0], prev[1]))
    prev = (m, pair)
for mmax, (a, b, c, d) in rows:
    assert b * c - a * d == 1 and a * L2 < b * L3 and c * L2 > d * L3
    M = M_of(c, d)
    ok = (N + 1) ** mmax * M < N ** mmax * (M + 1)
    ok_next = (N + 1) ** (mmax + 1) * M < N ** (mmax + 1) * (M + 1)
    print(f"m <= {mmax}: {a}/{b} < log2 3 < {c}/{d}, KBOUND = {b + d}, M = {M}, "
          f"size check {ok} (fails at m+1: {not ok_next})")
    for name, e in [("a", a), ("b", b), ("c", c), ("d", d)]:
        print(f"    {name} = 1048576 * {e >> 20} + {e & 1048575}")
