import cython

def f2(n: cython.int) -> cython.int:
    cdef int a = 0
    cdef int i
    for i in range(n):
        a += i
    return a
