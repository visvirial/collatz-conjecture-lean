// longstop_value.c: estimate the best ratio P/Q achievable by a potential mod 3^J.
// gcc -O2 -fopenmp -o longstop_value scripts/longstop_value.c && ./longstop_value 14 6000
// Undiscounted value iteration of the game (reward 1 per odd backward move, 0 per even move):
// V_{n+1}(s) = min over lifts t of s mod 3^(J+1) of max(V(2t), V((2t-1)/3) + 1 [t % 9 in {2, 8}]).
// min_s V_n(s) / n converges (from below, slowly) to the best ratio for modulus 3^J.
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
  int J = atoi(v[1]); int iters = atoi(v[2]);
  long M = 1; for (int i = 0; i < J; i++) M *= 3; long K = 3 * M;
  int *V = calloc(M, 4), *N = calloc(M, 4);
  for (int it = 1; it <= iters; it++) {
    long lo = 1L << 40, hi = -1;
    #pragma omp parallel for reduction(min:lo) reduction(max:hi) schedule(static)
    for (long s = 0; s < M; s++) {
      if (s % 3 == 0) { N[s] = 0; continue; }
      long best = 1L << 60;
      for (long t = s; t < K; t += M) {
        long cc = V[(2 * t) % M];
        if (t % 9 == 2 || t % 9 == 8) { long d = V[((2 * t - 1) / 3) % M] + 1; if (d > cc) cc = d; }
        if (cc < best) best = cc;
      }
      N[s] = best; if (best < lo) lo = best; if (best > hi) hi = best;
    }
    int *tmp = V; V = N; N = tmp;
    if (it % (iters / 10) == 0) printf("J=%d n=%d minV=%ld maxV=%ld min/n=%.5f\n", J, it, lo, hi, (double)lo / it);
  }
  return 0;
}
