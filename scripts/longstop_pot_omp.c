// longstop_pot_omp.c: OpenMP version of scripts/longstop_pot.c (same output format), for J up to ~16.
// gcc -O2 -fopenmp -o longstop_pot_omp scripts/longstop_pot_omp.c && ./longstop_pot_omp 14 8 17 h14.txt
// Capped value iteration for a bounded potential h on the units mod 3^J with, for every unit
// t mod 3^(J+1),  h(t) + P <= h(2t)  or  (t % 9 in {2, 8} and h(t) + P <= h((2t-1)/3) + Q).
// Prints H = max h, or "none" once the values drift below -100 Q J (no bounded potential).
// Writes h(0..3^J-1) (0 on multiples of 3), one per line, for scripts/gen_lsf.py.
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
  int J = atoi(v[1]); long P = atol(v[2]), Q = atol(v[3]);
  long M = 1; for (int i = 0; i < J; i++) M *= 3; long K = 3 * M;
  int *V = calloc(M, 4), *N = calloc(M, 4);
  for (int it = 0; it < 1000000; it++) {
    int ch = 0; long lo = 0;
    #pragma omp parallel for reduction(|:ch) reduction(min:lo) schedule(static)
    for (long s = 0; s < M; s++) {
      if (s % 3 == 0) { N[s] = 0; continue; }
      long best = 1L << 60;
      for (long t = s; t < K; t += M) {
        long cc = V[(2 * t) % M] - P;
        if (t % 9 == 2 || t % 9 == 8) { long d = V[((2 * t - 1) / 3) % M] + Q - P; if (d > cc) cc = d; }
        if (cc < best) best = cc;
      }
      if (best > 0) best = 0;
      N[s] = best; if (best != V[s]) ch = 1; if (best < lo) lo = best;
    }
    int *tmp = V; V = N; N = tmp;
    if (!ch) {
      printf("J=%d P/Q=%ld/%ld H=%ld it=%d\n", J, P, Q, -lo, it);
      if (c > 4) { FILE *f = fopen(v[4], "w"); for (long s = 0; s < M; s++) fprintf(f, "%ld\n", s % 3 ? V[s] - lo : 0); fclose(f); }
      return 0;
    }
    if (lo < -100 * Q * J) { printf("J=%d P/Q=%ld/%ld none it=%d\n", J, P, Q, it); return 1; }
  }
  printf("undecided\n"); return 2;
}
