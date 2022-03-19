import tarfile
import streamtar
from contextlib import contextmanager

archive_name = 'archive.tgz'

with tarfile.open(archive_name, mode='r') as archive_file:

    # list the contents to stdout
    members = archive_file.getmembers()
    archive_file.list()

    # count bytes of members
    for m in members:
        print(m.name, end='')
        with streamtar.open_tarfile_member(archive_file, m.name) as infile:
            if infile is None:
                print(': not a regular file')
            else:
                print(f': {sum(1 for c in infile.read())} bytes')
    
