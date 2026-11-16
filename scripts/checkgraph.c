/* Independent checker (C): reads "n m" then m edges "a b" (0-based); verifies a simple graph,
   prints min/max degree and the maximum number of common neighbours over all vertex pairs
   (a graph has no 4-cycle iff that maximum is <= 1). */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); int n, m;
  if (!f || fscanf(f, "%d %d", &n, &m) != 2) { printf("bad input\n"); return 1; }
  static unsigned char A[200][200];
  for (int k = 0; k < m; k++) { int a, b; if (fscanf(f, "%d %d", &a, &b) != 2 || a == b || a < 0 || b < 0 || a >= n || b >= n || A[a][b]) { printf("bad edge %d\n", k); return 1; } A[a][b] = A[b][a] = 1; }
  int mind = n, maxd = 0, maxc = 0;
  for (int v = 0; v < n; v++) { int d = 0; for (int u = 0; u < n; u++) d += A[v][u]; if (d < mind) mind = d; if (d > maxd) maxd = d; }
  for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) { int c = 0; for (int w = 0; w < n; w++) c += A[u][w] & A[v][w]; if (c > maxc) maxc = c; }
  printf("n=%d m=%d mindeg=%d maxdeg=%d max_common_neighbours=%d C4free=%s\n", n, m, mind, maxd, maxc, maxc <= 1 ? "yes" : "NO");
  return 0;
}
