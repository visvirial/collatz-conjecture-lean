#!/usr/bin/env python3
"""Potential for Collatz/LongStop.lean (Applegate-Lagarias style lower bound certificate).

Backward moves from a node a with 3 ∤ a: even a' = 2a; odd a' = (2a-1)/3 when a % 9 in {2, 8}.
We look for h on the units mod 3^J (values 0..H) such that for every unit s mod 3^(J+1)
  h(s mod 3^J) + P <= h(2s mod 3^J)                                   (even move), or
  s % 9 in {2,8} and h(s mod 3^J) + P <= h((2s-1)/3 mod 3^J) + Q        (odd move).
Then every node has an L-step backward path with P*L <= Q*(#odd moves) + H.
h is the greatest fixed point of V = min(0, B V) (values <= 0), shifted to be >= 0.
"""
J, P, Q = 5, 2, 5
M, K = 3 ** J, 3 ** (J + 1)
units = [s for s in range(M) if s % 3]
V = {s: 0 for s in units}
for it in range(10000):
    new = {}
    for s in units:
        best = None
        for t in range(s, K, M):  # lifts of s mod 3^(J+1)
            c = V[(2 * t) % M] - P
            if t % 9 in (2, 8):
                c = max(c, V[((2 * t - 1) // 3) % M] + Q - P)
            best = c if best is None else min(best, c)
        new[s] = min(0, best)
    if new == V:
        break
    V = new
    if min(V.values()) < -1000:
        raise SystemExit("no bounded potential")
lo = min(V.values())
h = [0] * M
for s in units:
    h[s] = V[s] - lo
H = max(h)
ok = True
for t in range(K):
    if t % 3 == 0:
        continue
    a = h[t % M] + P <= h[(2 * t) % M]
    b = t % 9 in (2, 8) and h[t % M] + P <= h[((2 * t - 1) // 3) % M] + Q
    ok &= a or b
print("iterations", it, "H =", H, "ok =", ok)
print(h)
