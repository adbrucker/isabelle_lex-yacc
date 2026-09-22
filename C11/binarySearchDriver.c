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
  int v;
  if ((scanf("%d", &v) != 1))
    {
      return 1;
    }
  int result = binarySearch(t, n, v);
  printf("%d\n", result);
  return 0;
}
