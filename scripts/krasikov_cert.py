#!/usr/bin/env python3
"""Find the constants used in Collatz/Krasikov.lean.

Hypothesis classes are residues mod 27; a node is known mod 81, which determines the
residues mod 27 of its children (2^a m - 1)/3 for 2 <= a <= A. We look for C_r > 0 with
  sum_a C_{child} (3/2^a)^c >= C_{s mod 27}   for every s mod 81 prime to 3,
then round to integers and check the integer form used by `krCert`.
"""
import math

c, M, K, A = 3 / 7, 27, 81, 30
cls = [r for r in range(M) if r % 3]


def kids(s):
    for a in range(2, A + 1):
        n = (2 ** a * s) % K
        if n % 9 in (4, 7):
            yield a, ((n - 1) // 3) % M


w = lambda a: (3 / 2 ** a) ** c
C = {r: 1.0 for r in cls}
for _ in range(3000):
    new = {r: min(sum(C[ch] * w(a) for a, ch in kids(s)) for s in range(r, K, M)) for r in cls}
    top = max(new.values())
    C = {r: new[r] / top for r in cls}

q = D = 10 ** 6
p = math.floor(2 ** (-c) * q) - 1
while p ** 7 * 8 > q ** 7:
    p -= 1
G = math.floor(3 ** c * D) - 1
while G ** 7 > 27 * D ** 7:
    G -= 1
Ci = {r: max(1, math.floor(C[r] * 10 ** 6)) for r in cls}
ok = all(sum(Ci[ch] * G * p ** a * q ** (A - a) for a, ch in kids(s)) >= Ci[s % M] * D * q ** A
         for s in range(K) if s % 3)
print("p =", p, "G =", G, "ok =", ok)
print([Ci.get(r, 0) for r in range(M)])
