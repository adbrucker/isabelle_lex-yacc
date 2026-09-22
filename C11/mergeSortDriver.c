#include <stdio.h>

int scanf(const char *format, ...);

#define N 100

int main(void )
{
  int t[N];
  int n = 0;
  while ((n < N))
    {
      if ((scanf("%d", &t[n]) != 1))
        {
          break;
        }
      n = (n + 1);
    }
  mergeSort(t, n, 0, n);
  for (int i = 0; (i < n); i = (i + 1))
    {
      printf("%d\n", t[i]);
    }
  return 0;
}
