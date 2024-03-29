from itertools import zip_longest

def merge(l1, l2, fillvalue=None):
    '''A generator that yields the elements of `l1` and `l2` alternatively.

    `l1` and `l2` are iterables
    `fillvalue` is yielded when one of `l1` and `l2` runs out, but not the other.

    The generator stops when all values of both `l1` and `l2` have been yielded.
    '''
    for a,b in zip_longest(l1, l2, fillvalue=fillvalue):
        yield a
        if len(b)>0:
            yield b

