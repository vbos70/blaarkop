# hs-checksum


## Build and use examples

Build:

    stack build
    stack build --profile
	
Command line usage:

    stack exec hs-checksum-exe < ../../LICENSE # or any other input file

In Windows Powershell:

    Get-Content ..\..\LICENSE | stack exec hs-checksum-exe

Timing the program:

    /usr/bin/time stack exec hs-checksum-exe < ../../LICENSE  
    time stack exec hs-checksum-exe < ../../LICENSE 

In Windows Powershell:

    Measure-Command { Get-Content ..\..\LICENSE | stack exec hs-checksum-exe }
    
Profiling the program:

    stack exec --profile -- hs-checksum-exe < ../../LICENSE  +RTS -p

This saves the profile to: ./hs-checksum-exe.prof:

    cat hs-checksum-exe.prof


