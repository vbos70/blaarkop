# Big List Mean

These examples are based on https://donsbot.wordpress.com/2008/06/04/haskell-as-fast-as-c-working-at-a-high-altitude-for-low-level-performance/

## Build and run the test

The default make target builds and runs (via *time*) the C and Haskell
versions:

	$ make
	cc -O2 -Wall -c blmean.c
	cc -O2 -Wall -o blmeanc blmean.o
	/usr/bin/time ./blmeanc 1e9 > report
	1.83user 0.00system 0:01.83elapsed 100%CPU (0avgtext+0avgdata 1732maxresident)k
	0inputs+8outputs (0major+65minor)pagefaults 0swaps
	ghc -O2 blmean_lowlevel.hs -optc-O2 --make
	[1 of 1] Compiling Main             ( blmean_lowlevel.hs, blmean_lowlevel.o )
	Linking blmean_lowlevel ...
	/usr/bin/time ./blmean_lowlevel 1e9 >> report
	1.78user 0.00system 0:01.78elapsed 100%CPU (0avgtext+0avgdata 3872maxresident)k
	0inputs+0outputs (0major+182minor)pagefaults 0swaps
	cat report
	500000000.067109
	500000000.067109

The 'clean' make target removes all files generated for the 'all'
target:

	$ make clean
	rm *.o *.hi blmean_lowlevel blmeanc report


## Analysis

Tp compute the mean of a list [1 ..n], we can use a formula, instead
of looping throug the list of numbers.

Example:


    1 + 2 + 3 + 4    == 10
	4 + 3 + 2 + 1    == 10
	-------------- +    -- +
	5 + 5 + 5 + 5    == 20   == (4 * (4+1)) / 2


    1 + 2 + 3 + 4 + 5   == 15
	4 + 3 + 2 + 1 + 5   == 15
	----------------- +    -- +
	5 + 5 + 5 + 5 + 10  == 30   == (5 * (5+1)) / 2 

In general:
	
	sum [1..n] == n*(n+1) / 2
	
See https://brilliant.org/wiki/formula-sum-_-i1-n-i-sum-_-i1-n-i-2-sum-_-i1-n-i-3/
	
