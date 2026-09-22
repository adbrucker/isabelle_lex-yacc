int binarySearch(int *t, int n, int v)
{
  int l = 0;
  int u = (n - 1);
  while ((l <= u))
    {
      int m = (l + ((u - l) / 2));
      if ((t[m] < v))
        {
          l = (m + 1);
        }
      else
        if ((t[m] > v))
          {
            u = (m - 1);
          }
        else
          {
            return m;
          }
    }
  return -1;
}
