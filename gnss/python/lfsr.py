from functools import reduce
from operator import xor
from itertools import islice
from functools import reduce

class LFSR:

    def __init__(self, initstate, coeffs, output=0):
        if output == 0:
            output = [len(initstate)]
        self.output = output
        self.coeffs = coeffs
        taps = [0] * len(initstate)
        for c in coeffs:
            taps[len(initstate)-c] = 1
        self.initstate = initstate[:]
        self.state = initstate[:]
        self.tap_indices = [i for (i,t) in enumerate(taps) if t == 1]
        self.output_indices = [ len(self.state) - i for i in output ]


    def taps(self):
        return [self.state[i] for i in self.tap_indices]


    
    # state:   0 0 1 0 1 1 0
    # coeffs:  . 6 5 . 3 . .
    # index    . 1 2 . 4 . .   : len(coeffs)-coeffs[i] 
    # taps:    0 1 1 0 1 0 0   : 1 + 2 + 4 
    # shift:  result = state[0], state := state[1:] + [xor(state[1], state[2], state[4]]   
    def __next__(self):

        v = reduce(xor, [self.state[i] for i in self.output_indices])
        self.state = self.state[1:] + [reduce(xor, self.taps())]
        return v

    def shift(self):
        return self.__next__()

    def __iter__(self):
        return self
        #c = LFSR(initstate=self.state, coeffs=self.coeffs, output=self.output)
        #return c



def demo_shift(s: LFSR):
    print(f'state:    {s.state}')
    print(f'indices:  {s.tap_indices}')

    taps = [s.state[i] for i in s.tap_indices]
    feedback = reduce(xor, taps)
    next(s)
    print(f'output: {reduce(xor, [s.state[i] for i in s.output_indices])}, reduce(xor{taps}): {feedback}')
    print(f'new state: {s.state}')

if __name__ == '__main__':
    l = LFSR([0,0,1,0,1,1,0], [5,3,2])
    for i in range(3):
        demo_shift(l)
        print()
