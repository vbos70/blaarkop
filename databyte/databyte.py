import struct
from collections import namedtuple
from typing import Dict, Tuple, Union

Field = namedtuple('Field', 'wd loc')
# Field.format: struct format string
# Field.loc: slice


class DataByteError(Exception): pass

class RawDataBytes(object):

    def __init__(self, rawbytes: bytearray, field: Dict[str, Field]):
        self._rawbytes = rawbytes
        self._field = field

        # TODO: check if properties are class or instance properties!!!!!
        for f in self._field:
            setattr(RawDataBytes, f, property(
                lambda self, f=f: self.__getitem__(f),
                lambda self, v, f=f: self.__setitem__(f, v),
                None,
                f'Field {f}: wd={self._field[f].wd}, loc={self._field[f].loc}'))

    def __getitem__(self, k: Union[int, slice, str]) -> Union[int, bytearray]:
        '''Returns self[k]

        If `k` is an `int` in the range(0,len(self)), then
        `self._rawbytes[k]` is returned. The return type is byte.

        If `k` is a `slice`, then `self._rawbytes[k]` is returned. The
        return type is bytearray.

        If `k` is a `str`, the bytes making up the field with name `k`
        is returned. The return type is bytearray.

        Otherwise, an IndexError is raised.

        '''
        if isinstance(k, int):
            return self._rawbytes[k]
        elif isinstance(k, slice):
            return self._rawbytes[k]
        else:
            return self._rawbytes[self._field[k].loc]

    def __setitem__(self, k: Union[int, slice, str], xs: Union[int, bytearray]):
        '''Sets self[k] to xs

        If `k` is an `int` in the range(0,len(self)), then
        `self._rawbytes[k]` is set to the byte `xs`.

        If `k` is a `slice` with the same number of elements as `xs`,
        then `self._rawbytes[k]` is set to the bytearray `xs`.

        If `k` is a `str`, the bytes making up the field with name `k`
        is set to the bytearray `xs`.

        Otherwise, an IndexError is raised.

        '''
        if isinstance(k, int):
            self._rawbytes[k] = xs
        elif isinstance(k, slice):
            self._rawbytes[k] = xs
        else:
            self._rawbytes[self._field[k].loc] = xs


################################################################################
#
# pytest unit test functions
#
# Run the unit tests as:
#
#     pytest databyte.py  # assuming pytest is installed!
#
###############################################################################

def ba(*args):
    '''Return a bytearray containing the values in `*args`.

    If `*args` contains exactly one element and if it is a list,
    this element (`args[0]`) is the argument to bytearray().

    Otherwise, the list `args` is the argument to bytearray().

    '''
    if len(args) == 1:
        if isinstance(args[0],list):
            args=args[0]
    return bytearray(args)

def make_db():
    return RawDataBytes(bytearray([0,1,2,3,4,5,6,7,8,9]),
                      {'a': Field(wd=1, loc=slice(0,1,1)),
                       'b': Field(wd=1, loc=slice(1,3,1)),
                       'cs': Field(wd=1, loc=slice(3,10,2)),
                       'ds': Field(wd=1, loc=slice(4,10,2))
                       })


def test_getitem():
    db = make_db()
    assert db['a'] == bytearray([0])
    assert db['b'] == bytearray([1,2])
    assert db['cs'] == bytearray([3,5,7,9])
    assert db['ds'] == bytearray([4,6,8])

def test_getitem_index():
    db = make_db()
    for i in range(10):
        assert db[i] == i

def test_getitem_slice():
    db = make_db()
    assert db[::2] == ba(list(range(0,10,2)))
    assert db[1::3] == ba(list(range(10))[1::3])
    assert db[-1::-1] == ba(list(range(10))[-1::-1])

def test_getitem_IndexError():
    db = make_db()
    try:
        x = db[100]
        assert False
    except IndexError:
        pass

    
def test_setitem_index():
    db = make_db()

    db[0] = 100
    assert db[0] == 100

    db[0::4] = ba(18,19,20)
    assert db[0::4] == ba(18, 19, 20)
    
def test_setitem_IndexError():
    db = make_db()
    try:
        db[100] == 100
        assert False
    except IndexError:
        pass


def test_setitem_slice_ValueError():
    db = make_db()

    try:
        assert len(db[0::4]) == 3
        db[0::4] = ba(19,39)
        assert False
    except ValueError:
        pass
    
    
def test_setitem():
    db = make_db()

    db['a'] = ba(100)
    assert db['a'] == bytearray([100])
    assert db[:] == bytearray([100,1,2,3,4,5,6,7,8,9])

    db['b'] = ba(13,14)
    assert db['b'] == bytearray([13,14])
    assert db[:] == bytearray([100,13,14,3,4,5,6,7,8,9])
    
    db['cs'] = ba(20,30,40,50)
    assert db['cs'] == bytearray([20,30,40,50])
    assert db[:] == bytearray([100,13,14,20,4,30,6,40,8,50])    

    db['ds'] = ba(200,201,202)
    assert db['ds'] == bytearray([200,201,202])

    assert db[:] == bytearray([100,13,14,20,200,30,201,40,202,50])
    

def test_field_access():

    db = make_db()

    assert db.a == bytearray([0])
    assert db.b == bytearray([1,2])
    assert db.cs == bytearray([3,5,7,9])
    assert db.ds == bytearray([4,6,8])


def test_field_assignment():

    db = make_db()

    db.a = ba(100)
    assert db.a == bytearray([100])

    db.b = ba(13,14)
    assert db.b == bytearray([13,14])

    db.cs = ba(20,30,40,50)
    assert db.cs == bytearray([20,30,40,50])

    db.ds = ba(200,201,202)
    assert db.ds == bytearray([200,201,202])

    assert db[:] == bytearray([100,13,14,20,200,30,201,40,202,50])    
