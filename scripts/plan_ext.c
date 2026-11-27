// Mirror of Collatz.resExt (Collatz/ExtDefs.lean) for planning the incremental extension.
// For each top-level residue r < 2^j0, simulate the sieve tree of depth d below it:
// at node (j, r) evaluate cert j r; if it fails and j < j0 + d, recurse into r and r + 2^j;
// at a leaf (j = j0 + d) check kdesc for n = 2^j m + r, M0 <= m < M1.
// Usage: plan_ext j0 d M0 M1 [fuel]
//   stdout: "r certIters leaves steps maxsteps" per top-level residue r
//   stderr: summary (also the cost of the flat design that evaluates cert at level j0+d only)
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static long certIters, certEvals, leaves, steps, maxsteps, fuelFail;
static long M0, M1, fuel;
// returns 1 iff cert k r = true; adds the number of certAux iterations to *it
static int cert(int k, u128 r, long *it) {
  u128 K = (u128)1 << k, a = K, b = r;
  for (int f = 0; f < 2 * k + 1; f++) {
    (*it)++;
    if (a % 2) return 0;
    if (b % 2 == 0) { a /= 2; b /= 2; } else { a = 3 * a; b = 3 * b + 1; }
    if (a < K && b <= r) return 1;
  }
  return 0;
}
static long desc(u128 n) {  // accelerated steps until < n, as kdesc counts them
  u128 x = n; long s = 0;
  do { if (x % 2 == 0) x = x / 2; else x = (3 * x + 1) / 2; s++; } while (x >= n);
  return s;
}
static void sieve(int d, int j, u128 r) {
  certEvals++;
  if (cert(j, r, &certIters)) return;
  if (d == 0) {
    leaves++;
    for (long m = M0; m < M1; m++) {
      u128 n = ((u128)m << j) + r;
      long s = desc(n);
      steps += s;
      if (s > maxsteps) maxsteps = s;
      if (s > fuel) fuelFail++;
    }
    return;
  }
  sieve(d - 1, j + 1, r);
  sieve(d - 1, j + 1, r + ((u128)1 << j));
}
int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: plan_ext j0 d M0 M1 [fuel]\n"); return 1; }
  int j0 = atoi(argv[1]), d = atoi(argv[2]);
  M0 = atol(argv[3]); M1 = atol(argv[4]); fuel = argc > 5 ? atol(argv[5]) : 1000;
  for (long r = 0; r < (1L << j0); r++) {
    long c0 = certIters, l0 = leaves, s0 = steps, mx0 = maxsteps;
    maxsteps = 0;
    sieve(d, j0, r);
    long mx = maxsteps;
    if (mx0 > maxsteps) maxsteps = mx0;
    printf("%ld %ld %ld %ld %ld\n", r, certIters - c0, leaves - l0, steps - s0, mx);
  }
  // flat design: cert at level j0 + d for every residue
  long flatIters = 0;
  int k = j0 + d;
  for (long r = 0; r < (1L << k); r++) cert(k, r, &flatIters);
  fprintf(stderr,
          "j0=%d d=%d M0=%ld M1=%ld fuel=%ld: certEvals=%ld certIters=%ld leaves(survivors)=%ld "
          "steps=%ld maxsteps=%ld overFuel=%ld | flat design certIters=%ld (2^%d evals)\n",
          j0, d, M0, M1, fuel, certEvals, certIters, leaves, steps, maxsteps, fuelFail, flatIters, k);
  return fuelFail != 0;
}
