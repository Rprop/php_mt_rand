#include <iostream>
#include <stdint.h>
#ifdef _WIN32
#include "time.h"
#else
#include <sys/time.h>
#endif
#ifdef _WIN32
#include <windows.h>
#include <process.h>
#endif

#define UNEXPECTED(c) (c)
#define MT_N          (624)
#define N             MT_N                 /* length of state vector */
#define M             (397)                /* a period parameter */
#define hiBit(u)      ((u) & 0x80000000U)  /* mask all but highest   bit of u */
#define loBit(u)      ((u) & 0x00000001U)  /* mask all but lowest    bit of u */
#define loBits(u)     ((u) & 0x7FFFFFFFU)  /* mask     the highest   bit of u */
#define mixBits(u, v) (hiBit(u)|loBits(v)) /* move hi bit of u to hi bit of v */

#define twist(m,u,v)  (m ^ (mixBits(u,v)>>1) ^ ((uint32_t)(-(int32_t)(loBit(v))) & 0x9908b0dfU))
#define twist_php(m,u,v)  (m ^ (mixBits(u,v)>>1) ^ ((uint32_t)(-(int32_t)(loBit(u))) & 0x9908b0dfU))


#define PHP_MT_RAND_MAX ((long) (0x7FFFFFFF)) /* (1<<31) - 1 */

#define MT_RAND_MT19937 0
#define MT_RAND_PHP 1


/*
 * A bit of tricky math here.  We want to avoid using a modulus because
 * that simply tosses the high-order bits and might skew the distribution
 * of random values over the range.  Instead we map the range directly.
 *
 * We need to map the range from 0...M evenly to the range a...b
 * Let n = the random number and n' = the mapped random number
 *
 * Then we have: n' = a + n(b-a)/M
 *
 * We have a problem here in that only n==M will get mapped to b which
 # means the chances of getting b is much much less than getting any of
 # the other values in the range.  We can fix this by increasing our range
 # artificially and using:
 #
 #               n' = a + n(b-a+1)/M
 *
 # Now we only have a problem if n==M which would cause us to produce a
 # number of b+1 which would be bad.  So we bump M up by one to make sure
 # this will never happen, and the final algorithm looks like this:
 #
 #               n' = a + n(b-a+1)/(M+1)
 *
 * -RL
 */
#define RAND_RANGE_BADSCALING(__n, __min, __max, __tmax) \
	(__n) = (__min) + (zend_long) ((double) ( (double) (__max) - (__min) + 1.0) * ((__n) / ((__tmax) + 1.0)))

#define RAND_RANGE(__n, __min, __max, __tmax) \
	(__n) = php_mt_rand_range((__min), (__max))

static void lcg_seed(void);
double php_combined_lcg(void);

#ifdef _WIN32
#define GENERATE_SEED() (((long) (time(0) * GetCurrentProcessId())) ^ ((long) (1000000.0 * php_combined_lcg())))
#else
#define GENERATE_SEED() (((long) (time(0) * getpid())) ^ ((long) (1000000.0 * php_combined_lcg())))
#endif


typedef VOID (WINAPI *MyGetSystemTimeAsFileTime)(LPFILETIME lpSystemTimeAsFileTime);

static MyGetSystemTimeAsFileTime timefunc = NULL;

static inline MyGetSystemTimeAsFileTime get_time_func(void)
{
	MyGetSystemTimeAsFileTime timefunc = NULL;
	HMODULE hMod = GetModuleHandle("kernel32.dll");

	if (hMod) {
		/* Max possible resolution <1us, win8/server2012 */
		timefunc = (MyGetSystemTimeAsFileTime)GetProcAddress(hMod, "GetSystemTimePreciseAsFileTime");

		if(!timefunc) {
			/* 100ns blocks since 01-Jan-1641 */
			timefunc = (MyGetSystemTimeAsFileTime)GetProcAddress(hMod, "GetSystemTimeAsFileTime");
		}
	}

	return timefunc;
}

BOOL php_win32_init_gettimeofday(void)
{
	timefunc = get_time_func();

	return (NULL != timefunc);
}

inline int getfilesystemtime(struct timeval *tv)
{
	FILETIME ft;
	unsigned __int64 ff = 0;
	ULARGE_INTEGER fft;

	timefunc(&ft);

        /*
	 * Do not cast a pointer to a FILETIME structure to either a
	 * ULARGE_INTEGER* or __int64* value because it can cause alignment faults on 64-bit Windows.
	 * via  http://technet.microsoft.com/en-us/library/ms724284(v=vs.85).aspx
	 */
	fft.HighPart = ft.dwHighDateTime;
	fft.LowPart = ft.dwLowDateTime;
	ff = fft.QuadPart;

	ff /= 10ull; /* convert to microseconds */
	ff -= 11644473600000000ull; /* convert to unix epoch */

	tv->tv_sec = (long)(ff / 1000000ull);
	tv->tv_usec = (long)(ff % 1000000ull);

	return 0;
}

int gettimeofday(struct timeval *time_Info, struct timezone *timezone_Info)
{
	/* Get the time, if they want it */
	if (time_Info != NULL) {
		getfilesystemtime(time_Info);
	}
	/* Get the timezone, if they want it */
	if (timezone_Info != NULL) {
		_tzset();
		timezone_Info->tz_minuteswest = _timezone;
		timezone_Info->tz_dsttime = _daylight;
	}
	/* And return */
	return 0;
}

/* mt_rand.c */
static uint32_t g_state[MT_N+1];  /* state vector + 1 extra to not violate ANSI C */
static uint32_t *g_next;       /* next random value is computed from here */
static int      g_left;        /* can *next++ this many times before reloading */

static bool mt_rand_is_seeded = 0; /* Whether mt_rand() has been seeded */
static long mt_rand_mode = MT_RAND_MT19937;

int32_t g_s1;
int32_t g_s2;
static int g_seeded = 0;

/*
 * combinedLCG() returns a pseudo random number in the range of (0, 1).
 * The function combines two CGs with periods of
 * 2^31 - 85 and 2^31 - 249. The period of this function
 * is equal to the product of both primes.
 */

#define MODMULT(a, b, c, m, s) q = s/a;s=b*(s-a*q)-c*q;if(s<0)s+=m

double php_combined_lcg(void) /* {{{ */
{
	int32_t q;
	int32_t z;

	if (!g_seeded) {
		lcg_seed();
	}

	MODMULT(53668, 40014, 12211, 2147483563L, g_s1);
	MODMULT(52774, 40692, 3791, 2147483399L, g_s2);

	z = g_s1 - g_s2;
	if (z < 1) {
		z += 2147483562;
	}

	return z * 4.656613e-10;
}
/* }}} */

static void lcg_seed(void) /* {{{ */
{
	struct timeval tv;

	if (gettimeofday(&tv, NULL) == 0) {
		g_s1 = tv.tv_sec ^ (tv.tv_usec<<11);
	} else {
		g_s1 = 1;
	}
#ifdef ZTS
	g_s2 = (long) tsrm_thread_id();
#else
	g_s2 = (long) getpid();
#endif

	/* Add entropy to s2 by calling gettimeofday() again */
	if (gettimeofday(&tv, NULL) == 0) {
		g_s2 ^= (tv.tv_usec<<11);
	}

	g_seeded = 1;
}


/* {{{ php_mt_initialize
 */
static inline void php_mt_initialize(uint32_t seed, uint32_t *state)
{
	/* Initialize generator state with seed
	   See Knuth TAOCP Vol 2, 3rd Ed, p.106 for multiplier.
	   In previous versions, most significant bits (MSBs) of the seed affect
	   only MSBs of the state array.  Modified 9 Jan 2002 by Makoto Matsumoto. */

	register uint32_t *s = state;
	register uint32_t *r = state;
	register int i = 1;

	*s++ = seed & 0xffffffffU;
	for( ; i < N; ++i ) {
		*s++ = ( 1812433253U * ( *r ^ (*r >> 30) ) + i ) & 0xffffffffU;
		r++;
	}
}
/* }}} */

/* {{{ php_mt_reload
 */
static inline void php_mt_reload(void)
{
	/* Generate N new values in state
	   Made clearer and faster by Matthew Bellew (matthew.bellew@home.com) */

	register uint32_t *state = g_state;
	register uint32_t *p = state;
	register int i;

	if (mt_rand_mode == MT_RAND_MT19937) {
		for (i = N - M; i--; ++p)
			*p = twist(p[M], p[0], p[1]);
		for (i = M; --i; ++p)
			*p = twist(p[M-N], p[0], p[1]);
		*p = twist(p[M-N], p[0], state[0]);
	}
	else {
		for (i = N - M; i--; ++p)
			*p = twist_php(p[M], p[0], p[1]);
		for (i = M; --i; ++p)
			*p = twist_php(p[M-N], p[0], p[1]);
		*p = twist_php(p[M-N], p[0], state[0]);
	}
	g_left = N;
	g_next = state;
}
/* }}} */

/* {{{ php_mt_srand
 */
void php_mt_srand(uint32_t seed)
{
	/* Seed the generator with a simple uint32 */
	php_mt_initialize(seed, g_state);
	php_mt_reload();

	/* Seed only once */
	mt_rand_is_seeded = 1;
}
/* }}} */

/* {{{ php_mt_rand
 */
uint32_t php_mt_rand(void)
{
	/* Pull a 32-bit integer from the generator state
	   Every other access function simply transforms the numbers extracted here */

	register uint32_t s1;

	if (UNEXPECTED(!mt_rand_is_seeded)) {
		php_mt_srand(GENERATE_SEED());
	}

	if (g_left == 0) {
		php_mt_reload();
	}
	--g_left;

	s1 = *g_next++;
	s1 ^= (s1 >> 11);
	s1 ^= (s1 <<  7) & 0x9d2c5680U;
	s1 ^= (s1 << 15) & 0xefc60000U;
	return ( s1 ^ (s1 >> 18) );
}
/* }}} */

int main(int argc, char** argv) 
{
	php_win32_init_gettimeofday();
	
	std::cout << "MT_RAND_MT19937" << std::endl;
	for (int i = 0; i < 5; ++i)
		std::cout << php_mt_rand() << std::endl;
	
	mt_rand_mode = MT_RAND_PHP;
	
	std::cout << "MT_RAND_PHP" << std::endl;
	for (int i = 0; i < 5; ++i)
		std::cout << php_mt_rand() << std::endl;
}
