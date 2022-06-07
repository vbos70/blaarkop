import struct
from collections import namedtuple
from typing import Dict

Field = namedtuple('Field', 'format loc')
# Field.format: struct format string
# Field.loc: slice

class RawDataBytes(object):

    def __init__(self, rawbytes: bytearray, field: Dict[str, slice]):
        self.rawbytes = rawbytes
        self.field = field

    def __getitem__(self, k: str):
        if isinstance(k, slice):
            return self.rawbytes[k]
        return self.rawbytes[self.field[k]]

    def __setitem__(self, k: str, xs: bytearray):
        self.rawbytes[self.field[k]] = xs


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
    '''Return a bytearray containing the values in *args.'''
    return bytearray(args)

def make_db():
    return RawDataBytes(bytearray([0,1,2,3,4,5,6,7,8,9]),
                      {'a': slice(0,1,1),
                       'b': slice(1,3,1),
                       'cs': slice(3,10,2),
                       'ds': slice(4,10,2)
                       })


def test_getitem():
    db = make_db()
    assert db['a'] == bytearray([0])
    assert db['b'] == bytearray([1,2])
    assert db['cs'] == bytearray([3,5,7,9])
    assert db['ds'] == bytearray([4,6,8])

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
    
