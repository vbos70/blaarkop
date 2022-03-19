import tarfile
from contextlib import contextmanager

@contextmanager
def open_tarfile_member(archive_file, fname):
    '''Context manager that returns an opened file for the tarfile member
    `fname` in tar archive `archive_file`.

    Note: if `fname` does not name a regular file in `archive_file`,
    None is returned.

    Usage:

    with open_tarfile_member(my_tar_file, member_name) as infile:
        bs = infile.read() # reads all bytes 
        ...

    '''
    f = archive_file.extractfile(fname)
    try:
        yield f
    finally:
        if f is not None:
            f.close()



        
