class bigprogram
{
	int g;
	
	void Main()
	{
		int b;
		b = square(2);
		print(b);
		print(fac(square(2)));
	}
  
	int square( int x )
	{
		int y;
		y = x*x;
		return y;   
	}
	
	int abs(int x)
	{
		
		if (x<0)
			x = 0-x;
		return x;
	}
  
	int fac(int x)
	{
		int r; int t;
		t=1; r=1;
		while (t<=x)
		{
			r = r*t;
			t = t+1;
		}
		return r;
	}
	
	
	int choose(int n, int k, int mod)
	{
		if (k > n)
			return 0;
		if (k > n / 2)
			k = n - k;
		double accum;
		accum = 1;
		int i;
		i = 1;
		while(i <= k)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
			i = i + 1;
		}
		return accum;
	}
	
	int numdivisors(int n) {
    int c;
		int j = 2;
		int ret = 1;
    while(j * j <= n) {
			if(n % j == 0) {
				c = 0;
				while(n % j == 0) {
					c = c + 1;
					n = n / j;
				}
				ret = ret * (c + 1);
			}
			j = j + 1;
    }
		if(n > 1) ret = ret * 2;
    return ret;
	}
	
	int choose2(int n, int k, int mod)
	{
		if (k > n)
			return 0;
		if (k > n / 2)
			k = n - k;
		double accum;
		accum = 1;
		int i;
		i = 1;
		while(i <= k)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
			i = i + 1;
		}
		return accum;
	}
	
	int numdivisors2(int n) {
    int c;
		int j = 2;
		int ret = 1;
    while(j * j <= n) {
			if(n % j == 0) {
				c = 0;
				while(n % j == 0) {
					c = c + 1;
					n = n / j;
				}
				ret = ret * (c + 1);
			}
			j = j + 1;
    }
		if(n > 1) ret = ret * 2;
    return ret;
	}
	
	int choose3(int n, int k, int mod)
	{
		if (k > n)
			return 0;
		if (k > n / 2)
			k = n - k;
		double accum;
		accum = 1;
		int i;
		i = 1;
		while(i <= k)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
			i = i + 1;
		}
		return accum;
	}
	
	int numdivisors3(int n) {
    int c;
		int j = 2;
		int ret = 1;
    while(j * j <= n) {
			if(n % j == 0) {
				c = 0;
				while(n % j == 0) {
					c = c + 1;
					n = n / j;
				}
				ret = ret * (c + 1);
			}
			j = j + 1;
    }
		if(n > 1) ret = ret * 2;
    return ret;
	}
	
	int choose4(int n, int k, int mod)
	{
		if (k > n)
			return 0;
		if (k > n / 2)
			k = n - k;
		double accum;
		accum = 1;
		int i;
		i = 1;
		while(i <= k)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
			i = i + 1;
		}
		return accum;
	}
	
	int numdivisors4(int n) {
    int c;
		int j = 2;
		int ret = 1;
    while(j * j <= n) {
			if(n % j == 0) {
				c = 0;
				while(n % j == 0) {
					c = c + 1;
					n = n / j;
				}
				ret = ret * (c + 1);
			}
			j = j + 1;
    }
		if(n > 1) ret = ret * 2;
    return ret;
	}
	
	int choose5(int n, int k, int mod)
	{
		if (k > n)
			return 0;
		if (k > n / 2)
			k = n - k;
		double accum;
		accum = 1;
		int i;
		i = 1;
		while(i <= k)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
			i = i + 1;
		}
		return accum;
	}
	
	int numdivisors5(int n) {
    int c;
		int j = 2;
		int ret = 1;
    while(j * j <= n) {
			if(n % j == 0) {
				c = 0;
				while(n % j == 0) {
					c = c + 1;
					n = n / j;
				}
				ret = ret * (c + 1);
			}
			j = j + 1;
    }
		if(n > 1) ret = ret * 2;
    return ret;
	}
}
