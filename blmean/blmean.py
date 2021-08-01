import sys



def mean(m, n):
    s = 0
    l = 0
    for x in range(m, n+1):
        s += x
        #l += 1
    return s / (n+1-m)
        
if __name__ == '__main__':

    a = float(sys.argv[1])
    print(mean(1, int(a)))
