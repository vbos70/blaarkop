import sys
import functools

def compute_CRC(bs: bytes) -> bytes:
    crc0 = 0
    crc1 = 0
    for b in bs:
        crc0 = (crc0 + b) % 256
        crc1 = (crc1 + crc0) % 256
    return (crc0, crc1)

def func_compute_CRC(bs: bytes):
    def f(crc, b):
        return (crc[0]+b, crc[1]+crc[0]+b)
    
    return functools.reduce(f, bs, (0,0))

if __name__ == '__main__':

    # use sys.stdin.buffer to read binary input from stdin
    crc0, crc1 = compute_CRC(sys.stdin.buffer.read())
    print(f"{crc0:02X} {crc1:02X}")
