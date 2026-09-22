void merge(int *t, int n, int l, int m, int u)
{
  int tmp[(u - l)];
  int i = l;
  int j = m;
  int k = 0;
  while (((i < m) || (j < u)))
    {
      if (((j >= u) || ((i < m) && (t[i] <= t[j]))))
        {
          tmp[k] = t[i];
          i = (i + 1);
        }
      else
        {
          tmp[k] = t[j];
          j = (j + 1);
        }
      k = (k + 1);
    }
  for (int p = 0; (p < (u - l)); p = (p + 1))
    {
      t[(l + p)] = tmp[p];
    }
}

void mergeSort(int *t, int n, int l, int u)
{
  if (((u - l) > 1))
    {
      int m = (l + ((u - l) / 2));
      mergeSort(t, n, l, m);
      mergeSort(t, n, m, u);
      merge(t, n, l, m, u);
    }
}
