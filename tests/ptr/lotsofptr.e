int f(int a,
      int b,
      int c,
      int d,
      int e,
      int ff,
      int g,
      int h,
      int i,
      int j,
      int k,
      int l,
      int m,
      int n,
      int o,
      int p,
      int q,
      int r,
      int *s,
      int t)
{
    if (t > 1)
    {
        *s = *s + 1;
        return 3 + f(a, b, c, d, d, g, ff, h + 1, i, j, k, l, m, n, p, o, q, q, s, t - 1);
    }
    return (k * (a + b * c + d + e + ff + g + h * i * j) + (l + m + n) + o + p * q) + (r + *s * t);
}

int main()
{
    int x1 = 1;
    int x2 = 3;
    int x3 = 3 + x1;
    int x4 = 4;
    int x5 = 5;
    int x6 = 6;
    int x7 = 7;
    int x8 = 8;
    int x9 = 9;
    int x10 = 10;
    int x11 = 11;
    int x12 = 12;
    int x13 = 13;
    int x14 = 14;
    int x15 = 15 + x4 - x3;
    int x16 = 16 * x1;
    int x17 = 17;
    int x18 = 18;
    int x19 = 19;
    int x20 = 20 * (x7 - x6);
    x1 = f(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, &x19, x20);
    int r = x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x16 + x17 + x18 + x19 + x20;
    print(r);
    return 1;
}
