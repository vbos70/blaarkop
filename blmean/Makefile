# Usage:
#     make
#     make clean
#     ARG=1e7 make   # specifies input value to blmean programs

all : report
	cat report

ARG ?= 1e9

report : blmeanc_report blmean_lowlevel_report blmean_highlevel1_report blmean_highlevel2_report

blmeanc_report : blmeanc
	echo  '# c' > report
	/usr/bin/time ./blmeanc $(ARG) >> report

blmean_highlevel1_report : blmean_highlevel1
	echo  '# hs highlevel1' >> report
	/usr/bin/time ./blmean_highlevel1 $(ARG) >> report

blmean_highlevel1 : blmean_highlevel1.hs
	ghc -O2 blmean_highlevel1.hs --make

blmean_highlevel2_report : blmean_highlevel2
	echo  '# hs highlevel2' >> report
	/usr/bin/time ./blmean_highlevel2 $(ARG) >> report

blmean_highlevel2 : blmean_highlevel2.hs
	ghc -O2 blmean_highlevel2.hs --make

blmean_highlevel3_report : blmean_highlevel3
	echo  '# hs highlevel3' >> report
	/usr/bin/time ./blmean_highlevel3 $(ARG) >> report

blmean_highlevel3 : blmean_highlevel3.hs
	ghc -O2 blmean_highlevel3.hs --make

blmean_lowlevel_report : blmean_lowlevel
	echo  '# hs lowlevel' >> report
	/usr/bin/time ./blmean_lowlevel $(ARG) >> report

blmean_lowlevel : blmean_lowlevel.hs
	ghc -O2 blmean_lowlevel.hs --make

blmeanc : blmean.o
	cc -O2 -Wall -o blmeanc blmean.o

blmean.o : blmean.c
	cc -O2 -Wall -c blmean.c

clean :
	rm *.o *.hi blmean_lowlevel blmean_highlevel1 blmean_highlevel2  blmean_highlevel3 blmeanc report
