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

def split(l, n):
    ''' Returns a list of sub-lists of iterator `l` such that each sub-list has 
    length `n`, except the final sub-list which might be shorter then `n`
    '''
    return [l[j:j+n] for j in range(0,len(l),n)]


class AttrDict(dict):
    '''Dictionaries with (str) keys as attributes.
    
    The attribute access `d.a` for `d : AttrDict` is resolved by first 
    looking up `a` according to normal attribute lookup rules. If `a` is not
    found, then `d[a]` is tried.
    '''

    def __getattr__(self, __name: str):
        if __name in self:
            return self[__name]
        raise AttributeError(f'Attribute {__name} was not found')

