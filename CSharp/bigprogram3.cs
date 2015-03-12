class bigprogram
{
	int g;
	
	void Main()
	{
		int b;
		b = square(2);
		print(abs(plus('a','b')));
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
		int r;
		r=1;
		for(int t=1;t<=x;t=t+1)
		{
			r = r*t;
		}
		return r;
	}
	
	int plus(int a, int b)
	{
		return a + b;
	}
	
	int choose(int n, int k, int mod)
	{
		if (k > n)
			return 0;
		if (k > n / 2)
			k = n - k;
		double accum;
		accum = 1;
		for(int i = 1; i <= k; i = i + 1)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
		}
		return accum;
	}
	
	int numdivisors(int n) {
		int ret = 1;
    for(int j = 2; j * j <= n; j = j + 1) {
			if(n % j == 0) {
				for(int c = 0; n % j == 0; c = c + 1) {
					n = n / j;
				}
				ret = ret * (c + 1);
			}
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
		for(int i = 1; i <= k; i = i + 1)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
		}
		return accum;
	}
	
	int numdivisors2(int n) {
		int ret = 1;
    for(int j = 2; j * j <= n; j = j + 1) {
			if(n % j == 0) {
				for(int c = 0; n % j == 0; c = c + 1) {
					n = n / j;
				}
				ret = ret * (c + 1);
			}
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
		for(int i = 1; i <= k; i = i + 1)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
		}
		return accum;
	}
	
	int numdivisors3(int n) {
		int ret = 1;
    for(int j = 2; j * j <= n; j = j + 1) {
			if(n % j == 0) {
				for(int c = 0; n % j == 0; c = c + 1) {
					n = n / j;
				}
				ret = ret * (c + 1);
			}
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
		for(int i = 1; i <= k; i = i + 1)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
		}
		return accum;
	}
	
	int numdivisors4(int n) {
		int ret = 1;
    for(int j = 2; j * j <= n; j = j + 1) {
			if(n % j == 0) {
				for(int c = 0; n % j == 0; c = c + 1) {
					n = n / j;
				}
				ret = ret * (c + 1);
			}
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
		for(int i = 1; i <= k; i = i + 1)
		{
			accum = accum * (n - k + i) / i;
			if (accum > mod)
			{
				int times;
				times = Floor(accum / mod);
				accum = accum - times * mod;
			}
		}
		return accum;
	}
	
	int numdivisors5(int n) {
		int ret = 1;
    for(int j = 2; j * j <= n; j = j + 1) {
			if(n % j == 0) {
				for(int c = 0; n % j == 0; c = c + 1) {
					n = n / j;
				}
				ret = ret * (c + 1);
			}
    }
		if(n > 1) ret = ret * 2;
    return ret;
	}
}
