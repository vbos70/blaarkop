c_checksum : c_checksum.o
	cc -Wall -o c_checksum c_checksum.o

main.o : c_checksum.c
	cc -Wall -c c_checksum.c

clean :
	rm *.o c_checksum

