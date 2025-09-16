from test_framework import *
from databyte import *



@test
def test_DataView():
    seq = list(range(100))

    dv = DataView(seq, 0, 100, 2, 2)


    try:
        _ = dv[-1]
    except IndexError as ie:
        test_print(ie)
        msg = str(ie)
    assert msg == 'DataView does not accept negative index: -1'

    try:
        dv[50]
    except IndexError as ie:
        test_print(ie)
        msg = str(ie)
    assert msg == 'DataView index too large: 50 (max is 49)', msg

    assert len(dv) == 50
    assert dv[4] == [8,9]

    assert dv[4:7] == [[8,9],[10,11],[12,13]], str(dv[4:7])

    assert dv[48] == [96,97]
    assert dv[49] == [98,99]

    assert dv[48::] == [[96,97], [98, 99]], str(dv[48::])
    try:
        assert dv[48:51:] == [[96,97], [98, 99]]#, str(dv[48:51:])
    except IndexError as ie:
        test_print(ie)
        msg = str(ie)
    assert msg == 'DataView slice stop index too large: slice(48, 51, None) (max is 50)', msg

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

@test
def test_getitem():
    db = make_db()
    assert db['a'] == [bytearray([0])]
    assert db['b'] == [bytearray([1]), bytearray([2])]
    assert db['cs'] == list(bytearray([i]) for i in [3,5,7,9])
    assert db['ds'] == list(bytearray([i]) for i in [4,6,8])

    db2 = make_db2()
    assert db2['a'] == [bytearray([0,1,2])]
    assert db2['b'] == [bytearray([3,4])]
    assert db2['cs'] == [bytearray([5,6]), bytearray([10,11]), bytearray([15,16])], str(db2['cs'])
    assert db2['ds'] == [bytearray([7,8,9]), bytearray([12,13,14]), bytearray([17,18,19])], str(db2['ds'])

@test
def test_getitem_index():
    db = make_db()
    for i in range(10):
        assert db[i] == i

@test
def test_getitem_slice():
    db = make_db()
    assert db[::2] == ba(list(range(0,10,2)))
    assert db[1::3] == ba(list(range(10))[1::3])
    assert db[-1::-1] == ba(list(range(10))[-1::-1])

@test
def test_getitem_IndexError():
    db = make_db()
    try:
        x = db[100]
        assert False
    except IndexError:
        pass

    
@test
def test_setitem_index():
    db = make_db()

    db[0] = 100
    assert db[0] == 100

    db[0::4] = ba(18,19,20)
    assert db[0::4] == ba(18, 19, 20)
    
@test
def test_setitem_IndexError():
    db = make_db()
    try:
        db[100] == 100
        assert False
    except IndexError:
        pass


@test
def test_setitem_slice_ValueError():
    db = make_db()

    assert len(db[0::4]) == 3
    try:
        db[0::4] = ba(19,39)
        assert False
    except ValueError:
        pass
    
    
@test
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
    

@test
def test_field_access():

    db = make_db()

    assert db.a == [bytearray([0])]
    assert db.b == list(ba(i) for i in [1,2])
    assert db.cs == list(ba(i) for i in [3,5,7,9])
    assert db.ds == list(ba(i) for i in [4,6,8])


@test
def test_field_assignment():

    db = make_db()

    db.a = [ba(100)]
    assert db.a == [bytearray([100])]

    assert len(db.b) == 2
    db.b = list(ba(i) for i in [13,14])
    assert db.b == list(ba(i) for i in [13,14])

    assert len(db.cs) == 4
    db.cs = list(ba(i) for i in [20,30,40,50])
    assert db.cs == list(ba(i) for i in [20,30,40,50])

    db.ds = list( ba(i) for i in [200,201,202])
    assert db.ds == list( ba(i) for i in [200,201,202])

    assert db[:] == bytearray([100,13,14,20,200,30,201,40,202,50])


@test
def test_multibyte_field():
    db = make_db2()

    #assert db.a == [ba(0,1,2)]
    #assert db.b == [ba(3,4)]

    #assert db.cs == [ba(5,6),ba(10,11), ba(15,16)]
    #assert db.ds == [ba(7,8,9), ba(12,13,14), ba(17,18,19)]

    #assert db.cs[0] == ba(5,6), str(db.cs[0])
    print(", ".join(":".join(hex(b) for b in ba) for ba in db.cs))
    db.cs[0] = ba(20,20)
    db.cs= [ba(20,20)] * 3
    assert db.a == [ba(0,1,2)]
    assert db.b == [ba(3,4)]

    assert db.cs == [ba(20,20), ba(20,20), ba(20,20)]
    assert db.ds == [ba(7,8,9), ba(12,13,14), ba(17,18,19)]

    #assert db.cs == [ba(20,20),ba(10,11), ba(15,16)], ", ".join(":".join(hex(b) for b in ba) for ba in db.cs)
    
#@test
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


if __name__ == '__main__':
    run_tests(print_summary_only=False, new_suppress_test_output=False)
    print(test_summary())
