void swap(int *t, int n, int i, int j)
{
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
}

void selectionSort(int *t, int n)
{
  for (int i = 0; (i < n); i = (i + 1))
    {
      int min = i;
      for (int j = (i + 1); (j < n); j = (j + 1))
        {
          if ((t[j] < t[min]))
            {
              min = j;
            }
        }
      swap(t, n, i, min);
    }
}
