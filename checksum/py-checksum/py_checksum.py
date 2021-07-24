import sys


def compute_CRC(bs: bytes) -> bytes:
    crc0 = 0
    crc1 = 0
    for b in bs:
        crc0 = (crc0 + b) % 256
        crc1 = (crc1 + crc0 + b) % 256
    return (crc0, crc1)


if __name__ == '__main__':

    # use sys.stdin.buffer to read binary input from stdin
    crc0, crc1 = compute_CRC(sys.stdin.buffer.read())
    print(f"{crc0:02X} {crc1:02X}")
