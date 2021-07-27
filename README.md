# Blaarkop

This repository contains programming examples.

About the name: *Blaarkop* is a Dutch breed of dairy cattle, see
https://en.wikipedia.org/wiki/Blaarkop or in Dutch
https://nl.wikipedia.org/wiki/Blaarkop. Blaarkop are not known to have
programming skills.

## Checksum

The *checksum* example contains different implementations of a
checksum algorithm. The specification of the algorithm is:

    input: byte[0..n)

    crc0 = 0
    crc1 = 0
    for b <- byte[0..n) do
        crc0 = (crc0 + b) mod 256
        crc1 = (crc1 + crc0 + b) mod 256

    output: (crc0, crc1)

Given an input sequence of `n` bytes, `byte[0], byte[1], ...,
byte[n-1]`, the algorithm computes an output of two bytes `crc0` and
`crc1`.

The goal of the example is to compare different implementations:

- speed,
- memory usage,
- readability

## Big List Mean

The *blmean* example contains programs to compute the mean of a big
list of 64-bits real numbers. The examples are taken from
https://donsbot.wordpress.com/2008/06/04/haskell-as-fast-as-c-working-at-a-high-altitude-for-low-level-performance/. The
goal of the example is to understand and verify that blog post.

## Generic instructions

### Git

Push commits:

    $ git push

This assumes you have read/write privileges at the remote repository.

### Linux

Time a program:

    $ /usr/bin/time programename < inputfile # GNU time
    $ time programename < inputfile          # shell's built-in time

Generate 100M of random bytes:

    $ cat /dev/urandom | head -c 100M > log100M.bin

See man head for syntax of the argument of *head -c*.

### C projects

    $ mkdir my_project_name  # a new directory for each project
	
Next, create a Makefile in the new directory and write the C source
code.

### Haskell projects

Create a new project with stack:

    $ stack new my-project-name
	$ cd my-project-name

Build the project:

    $ stack build
	$ stack build --profile # to generate performance profile
	
Execute programs

    $ stack exec my-project-name-exe
	$ stack exec --profile -- my-project-name-exe +RTS -p
	
## Python project

Note: The Python code in this repository is written for *Python 3*.

    $ mkdir my_project_name  # a new directory for each project
    $ cd my_project_name
