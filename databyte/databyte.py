import struct
from collections import namedtuple
from typing import Dict, List, Tuple, Union

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

    def __str__(self):
        return ":".join(f"{f}={[list(i) for i in self[f]]}" for f in self._field)

    def __getitem__(self, k: Union[int, slice, str]) -> Union[int, bytearray]:
        '''Returns self[k]

        If `k` is an `int` in the range(0,len(self)), then
        `self._rawbytes[k]` is returned. The return type is byte.

        If `k` is a `slice`, then `self._rawbytes[k]` is returned. The
        return type is bytearray.

        If `k` is a `str`, the bytes making up the field with name `k`
        is returned. The return type is List[bytearray].

        Otherwise, an IndexError is raised.

        '''
        if isinstance(k, int):
            return self._rawbytes[k]
        elif isinstance(k, slice):
            return self._rawbytes[k]
        else:
            wd,loc = self._field[k]
            field_idx = list(range(len(self._rawbytes)))[loc]
            repeat = (loc.stop-loc.start+loc.step-1) // loc.step
            return list(self._rawbytes[i:i+wd] for i in field_idx)


    def __setitem__(self, k: Union[int, slice, str], xs: Union[int, List[bytearray]]):
        '''Sets self[k] to xs

        If `k` is an `int` in the range(0,len(self)), then
        `self._rawbytes[k]` is set to the byte `xs`.

        If `k` is a `slice` with the same number of elements as `xs`,
        then `self._rawbytes[k]` is set to the bytearray `xs`.

        If `k` is a `str`, the bytes making up the field with name `k`
        is set to the List[bytearray] `xs`.

        Otherwise, an IndexError is raised.

        '''
        if isinstance(k, int):
            self._rawbytes[k] = xs
        elif isinstance(k, slice):
            self._rawbytes[k] = xs
        else:
            wd,loc = self._field[k]
            repeat = (loc.stop-loc.start+loc.step-1) // loc.step
            if len(xs) != repeat:
                raise ValueError(f"Incorrect number of values in assignment to Field {k}, expected {repeat}, found {len(xs)}.")
            for i in range(repeat):
                if wd != len(xs[i]):
                    raise ValueError(f"Incorrect number of bytes in assignment to Field {k}[{i}], expected {wd}, found {len(xs[i])}.")
                idx = loc.start + i*loc.step
                self._rawbytes[idx:idx+wd] = xs[i]

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
                      {'a': Field(wd=1, loc=slice(0,1,1)),   # 1 byte at position 0 
                       'b': Field(wd=1, loc=slice(1,3,1)),   # 2 bytes at positions 1,2
                       'cs': Field(wd=1, loc=slice(3,10,2)), # 4 bytes at positions 3,5,7,9
                       'ds': Field(wd=1, loc=slice(4,10,2))  # 3 bytes at positions 4,6,8
                       })

Group = namedtuple('Group', 'offset length repeat')
def total_length(g):
    return g.length * g.repeat

def make_db2():
    g0 = Group(offset=0, length=5, repeat=1)
    g1 = Group(offset=total_length(g0), length=5, repeat=3)

    return RawDataBytes(bytearray(list(range(total_length(g0) + total_length(g1)))),
                      {'a': Field(wd=3, loc=slice(g0.offset+0, g0.offset+total_length(g0), g0.length)),
                       'b': Field(wd=2, loc=slice(g0.offset+3, g0.offset+total_length(g0), g0.length)),
                       'cs': Field(wd=2, loc=slice(g1.offset+0, g1.offset+total_length(g1), g1.length)),
                       'ds': Field(wd=3, loc=slice(g1.offset+2, g1.offset+total_length(g1), g1.length))
                       })


def test_getitem():
    db = make_db()
    assert db['a'] == [bytearray([0])]
    assert db['b'] == [bytearray([1]), bytearray([2])]
    assert db['cs'] == list(bytearray([i]) for i in [3,5,7,9])
    assert db['ds'] == list(bytearray([i]) for i in [4,6,8])

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

    db['a'] = [ba(100)]
    assert db['a'] == [bytearray([100])]
    assert db[:] == bytearray([100,1,2,3,4,5,6,7,8,9])

    db['b'] = [ba(13), ba(14)]
    assert db['b'] == list(bytearray([i]) for i in [13,14])
    assert db[:] == bytearray([100,13,14,3,4,5,6,7,8,9])
    
    db['cs'] = list(ba(i) for i in [20,30,40,50])
    assert db['cs'] == list(ba(i) for i in [20,30,40,50])
    assert db[:] == bytearray([100,13,14,20,4,30,6,40,8,50])    

    db['ds'] = list(ba(i) for i in [200,201,202])
    assert db['ds'] == list(ba(i) for i in [200,201,202])

    assert db[:] == bytearray([100,13,14,20,200,30,201,40,202,50])
    

def test_field_access():

    db = make_db()

    assert db.a == [bytearray([0])]
    assert db.b == list(ba(i) for i in [1,2])
    assert db.cs == list(ba(i) for i in [3,5,7,9])
    assert db.ds == list(ba(i) for i in [4,6,8])


def test_field_assignment():

    db = make_db()

    db.a = [ba(100)]
    assert db.a == [bytearray([100])]

    db.b = list(ba(i) for i in [13,14])
    assert db.b == list(ba(i) for i in [13,14])

    db.cs = list(ba(i) for i in [20,30,40,50])
    assert db.cs == list(ba(i) for i in [20,30,40,50])

    db.ds = list( ba(i) for i in [200,201,202])
    assert db.ds == list( ba(i) for i in [200,201,202])

    assert db[:] == bytearray([100,13,14,20,200,30,201,40,202,50])


def test_multibyte_field():
    db = make_db2()

    assert db.a == [ba(0,1,2)]
    assert db.b == [ba(3,4)]

    assert db.cs == [ba(5,6),ba(10,11), ba(15,16)]
    assert db.ds == [ba(7,8,9), ba(12,13,14), ba(17,18,19)]

    db.cs[0] = ba(20,20)
    assert db.cs == [ba(20,20),ba(10,11), ba(15,16)]
    
def test_multibyte_field_setitem():
    db = make_db2()

    expected = list(range(20))
    assert db[:] == bytearray(expected)
    
    assert db.a == [ba(0,1,2)]
    assert db.b == [ba(3,4)]
    
    db.a = [ba(2,1,0)]
    expected[0:3] = [2,1,0]
    assert db[:] == bytearray(expected)

    db.b = [ba(30,40)]
    expected[3:5] = [30,40]
    assert db[:] == bytearray(expected)
    
    assert db.a == [ba(2,1,0)]
    assert db.b == [ba(30,40)]

    db.cs = [ba(50,60), ba(100,110), ba(150,160)]
    expected[5:7] = [50,60]
    expected[10:12] = [100,110]
    expected[15:17] = [150,160]
    assert db[:] == bytearray(expected)
    
    db.ds = [ba(0,0,0), ba(1,1,1),ba(2,2,2)]
    expected[7:10] = [0,0,0]
    expected[12:15] = [1,1,1]
    expected[17:20] = [2,2,2]
    assert db[:] == bytearray(expected)
    
    assert db.cs == [ba(50,60), ba(100,110), ba(150,160)]
    assert db.ds == [ba(0,0,0), ba(1,1,1), ba(2,2,2)]
    
