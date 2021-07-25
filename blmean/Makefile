all : report
	cat report

report : blmeanc_report blmean_lowlevel_report

blmeanc_report : blmeanc
	/usr/bin/time ./blmeanc 1e9 > report

blmean_lowlevel_report : blmean_lowlevel
	/usr/bin/time ./blmean_lowlevel 1e9 >> report

blmean_lowlevel : blmean_lowlevel.hs
	ghc -O2 blmean_lowlevel.hs -optc-O2 --make

blmeanc : blmean.o
	cc -O2 -Wall -o blmeanc blmean.o

blmean.o : blmean.c
	cc -O2 -Wall -c blmean.c

clean :
	rm *.o *.hi blmean_lowlevel blmeanc report
