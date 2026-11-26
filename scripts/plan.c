// Mirror of Collatz.cert / resCheck: for residues r mod 2^k, report whether cert passes and,
// for survivors, the total and max number of steps kdesc needs for n = 2^k m + r, m < M.
// Usage: plan k M  -> prints "r steps maxsteps" for each survivor, and a summary on stderr.
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static int cert(int k, u128 r) {
  u128 K = (u128)1 << k, a = K, b = r;
  for (int f = 0; f < 2 * k + 1; f++) {
    if (a % 2) return 0;
    if (b % 2 == 0) { a /= 2; b /= 2; } else { a = 3 * a; b = 3 * b + 1; }
    if (a < K && b <= r) return 1;
  }
  return 0;
}
static long desc(u128 n) {  // steps until < n (n >= 2)
  u128 x = n; long s = 0;
  do { x = (x % 2 == 0) ? x / 2 : 3 * x + 1; s++; } while (x >= n);
  return s;
}
int main(int argc, char **argv) {
  int k = atoi(argv[1]); long M = atol(argv[2]);
  long total = 0, mx = 0, nsurv = 0;
  for (long r = 0; r < (1L << k); r++) {
    if (cert(k, r)) { if (r >= 2) { long s = desc(r); total += s; if (s > mx) mx = s; } continue; }
    nsurv++;
    long t = 0, m2 = 0;
    for (long m = 0; m < M; m++) {
      u128 n = ((u128)m << k) + r;
      if (n < 2) continue;
      long s = desc(n); t += s; if (s > m2) m2 = s;
    }
    printf("%ld %ld %ld\n", r, t, m2);
    total += t; if (m2 > mx) mx = m2;
  }
  fprintf(stderr, "k=%d M=%ld survivors=%ld total_steps=%ld max_steps=%ld\n", k, M, nsurv, total, mx);
  return 0;
}
