# Blaarkop

This reposiory contains programming examples.

About the name: *Blaarkop* is a Dutch breed of dairy cattle, see
https://en.wikipedia.org/wiki/Blaarkop or in Dutch
https://nl.wikipedia.org/wiki/Blaarkop.

## Checksum



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
