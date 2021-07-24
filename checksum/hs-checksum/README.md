# hs-checksum


## Build and use examples

Build:

    stack build
    stack build --profile
	
Command line usage:

    stack exec hs-checksum-exe < src/Lib.hs # or any other input file

Timing the program:

    /usr/bin/time stack exec hs-checksum-exe < src/Lib.hs 
    time stack exec hs-checksum-exe < src/Lib.hs 
	
Profiling the program:

    stack exec --profile -- hs-checksum-exe < src/Lib.hs +RTS -p

This saves the profile to: ./hs-checksum-exe.prof:

    cat hs-checksum-exe.prof


