from lfsr import LFSR
from operator import xor
from typing import Generator

# Define the feedback taps of GPS G2 coder per PRN
# from: Table 3-Ia https://www.gps.gov/technical/icwg/IS-GPS-200J.pdf
prn_out_taps = {
    1: [2, 6],    2: [3, 7],    3: [4, 8],    4: [5, 9],    5: [1, 9],    6: [2, 10],    7: [1, 8],    8: [2, 9],
    9: [3, 10],   10: [2, 3],  11: [3, 4],   12: [5, 6],   13: [6, 7],   14: [7, 8],    15: [8, 9],   16: [9, 10],
    17: [1, 4],   18: [2, 5],  19: [3, 6,],  20: [4, 7],   21: [5, 8],   22: [6, 9],    23: [1, 3],   24: [4, 6],
    25: [5, 7],   26: [6, 8],  27: [7, 9],   28: [8, 10],  29: [1, 6],   30: [2, 7],    31: [3, 8],   32: [4, 9]
}


GPS_L1_PRNS = list(prn_out_taps.keys())

def GPS_L1_coder(prn: int) -> Generator[int, None, None]:
    '''
    Returns a generator for the GPS L1 C/A prn code of the given `prn` number.
    
    PRN numbers are defined in https://www.gps.gov/technical/icwg/IS-GPS-200J.pdf
    '''
    G1 = LFSR([1] * 10, [3, 10] ,[10])
    G2 = LFSR([1]*10, [2, 3, 6, 8, 9, 10], prn_out_taps[prn])
    yield from (xor(a,b) for (a,b) in zip(G1, G2)) 


def test_GPS_L1_coder(prn: int) -> bool:
    first_10_chips = {
        1: 0o1440,     2: 0o1620,      3: 0o1710,      4: 0o1744,      5: 0o1133,      6: 0o1455,      7: 0o1131,      8: 0o1454,
        9: 0o1626,    10: 0o1504,     11: 0o1642,     12: 0o1750,     13: 0o1764,     14: 0o1772,     15: 0o1775,     16: 0o1776,
        17: 0o1156,   18: 0o1467,     19: 0o1633,     20: 0o1715,     21: 0o1746,     22: 0o1763,     23: 0o1063,     24: 0o1706,
        25: 0o1743,   26: 0o1761,     27: 0o1770,     28: 0o1774,     29: 0o1127,     30: 0o1453,     31: 0o1625,     32: 0o1712
    }
    from itertools import islice
    chips = f'{first_10_chips[prn]:010b}'
    coder_chips = "".join(str(i) for i in islice(GPS_L1_coder(prn), 0,10))
    assert chips == coder_chips, f'PRN({prn}) coder: incorrect chips: {coder_chips}, expected: {chips}'

if __name__ == '__main__':
    from itertools import islice
    print(list(islice(GPS_L1_coder(1), 10)))
    for prn in GPS_L1_PRNS:
        try:
            test_GPS_L1_coder(prn)
            print(f'PRN({prn}): OK')
        except Exception as e:
            print(f'PRN({prn}): Failed:')
            print(e)