// longstop_pot.c: fast C version of scripts/longstop_cert.py for large moduli.
// gcc -O2 -o longstop_pot scripts/longstop_pot.c && ./longstop_pot 12 6 13 h12.txt
// writes the potential h(0..3^J-1) (0 on multiples of 3), one per line, for scripts/gen_ls12.py.
// ratio.c J P Q: is there a bounded potential h on units mod 3^J with, for every unit t mod 3^(J+1),
//   h(t) + P <= h(2t)  or  (t%9 in {2,8} and h(t) + P <= h((2t-1)/3) + Q)  ?  prints H or "none".
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
  int J = atoi(v[1]), P = atoi(v[2]), Q = atoi(v[3]);
  long M = 1, K; for (int i = 0; i < J; i++) M *= 3; K = 3 * M;
  long *V = calloc(M, sizeof(long)), *N = calloc(M, sizeof(long));
  for (int it = 0; it < 400000; it++) {
    int ch = 0; long lo = 0;
    for (long s = 0; s < M; s++) {
      if (s % 3 == 0) continue;
      long best = 1L << 60;
      for (long t = s; t < K; t += M) {
        long cc = V[(2 * t) % M] - P;
        if (t % 9 == 2 || t % 9 == 8) { long d = V[((2 * t - 1) / 3) % M] + Q - P; if (d > cc) cc = d; }
        if (cc < best) best = cc;
      }
      if (best > 0) best = 0;
      N[s] = best; if (best != V[s]) ch = 1; if (best < lo) lo = best;
    }
    long *tmp = V; V = N; N = tmp;
    if (!ch) { printf("J=%d P/Q=%d/%d H=%ld it=%d\n", J, P, Q, -lo, it); if (c > 4) { FILE *f = fopen(v[4], "w"); for (long s = 0; s < M; s++) fprintf(f, "%ld\n", s % 3 ? V[s] - lo : 0); fclose(f); } return 0; }
    if (lo < -20000) { printf("J=%d P/Q=%d/%d none\n", J, P, Q); return 1; }
  }
  printf("J=%d P/Q=%d/%d undecided\n", J, P, Q); return 2;
}
