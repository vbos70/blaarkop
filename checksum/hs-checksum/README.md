# checksum


## examples

Build:

    stack build
    stack build --profile
	
Command line usage:

    stack exec checksum-exe < ../bin-packets/generated_packets_100M.bin 

Timing the program:

    /usr/bin/time  stack exec checksum-exe < ../bin-packets/generated_packets_100M.bin 
	
Profiling the program:

    stack exec --profile -- checksum-exe < ../bin-packets/generated_packets_100M.bin +RTS -p

This saves the profile to: ./checksum-exe.prof

