#!/usr/bin/env python3
"""Certificates for Collatz/ApplegateLagariasSemigroup.lean (Applegate-Lagarias, 3x+1 semigroup).

Default: for every q < 2^15 with gcd(q, 6) = 1, q >= 17 and q not in H, find odd f1, f2 < q,
both prime to 3, with q | 3 f1 f2 + 1 (then q is wild once f1, f2 are wild and
(3 f1 f2 + 1) / q lies in the 3x+1 semigroup S).  The pair is packed as f1 + 128 f2 (22 bits)
at index q // 3 of one natural number, printed as the Lean definition `alCert`.

With `--rows`: search multiplier sequences for the residue classes of Tables 1-2 of the paper
(Lemma 2.1) and print them as the Lean list `alRows`.

Usage: python3 scripts/al_semigroup_cert.py [--rows]
"""
import math
import sys

Q0 = 1 << 15
H = [5, 7, 11, 13, 23, 29, 43]
SKIP = set(H)
W = 22

# (s, K): the classes s mod 2^K of Tables 1 and 2 (a prefix code covering all classes
# mod 4096 except -1).
CLASSES = [(0, 1), (1, 2), (3, 4), (11, 5), (27, 7), (91, 8), (219, 8), (59, 7), (123, 8),
           (251, 8), (7, 6), (39, 7), (103, 9), (359, 9), (231, 8), (23, 5), (15, 7), (79, 8),
           (207, 8), (47, 7), (111, 7), (31, 6), (63, 7), (127, 8), (255, 9), (511, 10),
           (1023, 11), (2047, 12)]


def cert(q):
    r = (-pow(3, -1, q)) % q
    for f1 in range(1, 128):
        if f1 % 2 == 0 or f1 % 3 == 0 or math.gcd(f1, q) != 1:
            continue
        f2 = r * pow(f1, -1, q) % q
        if f2 % 2 == 1 and f2 % 3 != 0:
            assert (3 * f1 * f2 + 1) % q == 0
            return f1, f2
    raise ValueError(q)


def fin_ok(K, s, A, B):
    m0 = 1 if s <= 1 else 0
    return 79 * A <= 76 * 2 ** K and 79 * (A * m0 + B) <= 76 * (2 ** K * m0 + s)


def search(K, s, a, b, steps, mults, ops):
    """ops: 0 = one step of T, h = multiplication by h; K steps of T in total."""
    if steps == K:
        return ops if fin_ok(K, s, a, b) else None
    if b % 2 == 0:
        r = search(K, s, a // 2, b // 2, steps + 1, mults, ops + [0])
    else:
        r = search(K, s, 3 * a // 2, (3 * b + 1) // 2, steps + 1, mults, ops + [0])
    if r:
        return r
    if mults > 0:
        for h in H:
            r = search(K, s, h * a, h * b, steps, mults - 1, ops + [h])
            if r:
                return r
    return None


def rows():
    for r in range(4096):
        c = [1 for (s, K) in CLASSES if r % 2 ** K == s]
        assert len(c) == (0 if r == 4095 else 1), r
    out = []
    for (s, K) in CLASSES:
        for M in range(4):
            ops = search(K, s, 2 ** K, s, 0, M, [])
            if ops is not None:
                break
        assert ops is not None, (s, K)
        out.append(f"({s}, {K}, {ops})")
    print("def alRows : List (Nat × Nat × List Nat) :=\n  [" + ",\n   ".join(out) + "]")


def main():
    sys.set_int_max_str_digits(0)
    if "--rows" in sys.argv:
        rows()
        return
    big = 0
    n = 0
    for q in range(1, Q0):
        if q % 2 == 0 or q % 3 == 0 or q < 17 or q in SKIP:
            continue
        f1, f2 = cert(q)
        big |= (f1 + 128 * f2) << (W * (q // 3))
        n += 1
    print(f"-- {n} certificates, {big.bit_length()} bits", file=sys.stderr)
    print(f"def alCert : Nat := {big}")


if __name__ == "__main__":
    main()
