import struct
from collections import namedtuple
from typing import Dict, List, Tuple, Union

Field = namedtuple('Field', 'wd loc')
# Field.format: struct format string
# Field.loc: slice


class DataByteError(Exception): pass

def identity(x):
    return x

class DataView:

    def __init__(self, sequence, start, end, step, width, to_sequence=identity, from_sequence=identity):
        self.sequence = sequence
        self.start = start
        self.end = end 
        self.step = step
        self.width = width
        self.to_sequence = to_sequence
        self.from_sequence = from_sequence
    
    def __len__(self):
        return (self.end-self.start)//self.step
    
    def __getitem__(self, i):
        if isinstance(i, int):
            if i<0:
                raise IndexError(f'DataView does not accept negative index: {i}')
            if i>=len(self):
                raise IndexError(f'DataView index too large: {i} (max is {len(self)-1})')
            return self.from_sequence(self.sequence[i*self.step: i*self.step + self.width])
        elif isinstance(i, slice):
            i_start = i.start if i.start is not None else 0
            i_stop = i.stop if i.stop is not None else len(self)
            i_step = i.step if i.step is not None else 1

            if i_start < 0:
                raise IndexError(f'DataView does not accept slice with negative start index: {i}')
            elif i_stop>len(self):
                raise IndexError(f'DataView slice stop index too large: {i} (max is {len(self)})')
            else:
                return self.from_sequence(
                        list(self.sequence[j*self.step: j*self.step + self.width]
                           for j in range(i_start, i_stop, i_step)))
        else:
            raise IndexError(f"Index or slice expected, not {type(i)}") 
    
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
        print('__getitem__')
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
        print('__setitem__')
        if isinstance(k, int):
            print('##')
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
