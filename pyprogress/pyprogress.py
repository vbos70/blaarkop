# The progress() function is based on:
#     https://gist.github.com/vladignatyev/06860ec2040cb497f0f3
import sys


def progress(count, total, prefix='', postfix=''):
    '''Updates sys.stdout with the next line of the progress animation.

    count: int current share of the total prpgress.

    total: int maximum progress value.

    prefix: str message to print to the left of sym.

    postfix: str message to print to the right of sym.

    Returns: None

    As an example how to use this function, see progress_demo().
    '''
    bar_len = 60
    filled_len = int(round(bar_len * count / float(total)))

    percents = round(100.0 * count / float(total), 1)
    bar = '=' * filled_len + '-' * (bar_len - filled_len)

    sys.stdout.write('%s[%s] %s%s%s\r' % (prefix, bar, percents, '%', postfix))
    sys.stdout.flush()

    
def busy(sym, prefix='', postfix='', num_chr_clear=0):
    '''Updates sys.stdout with the next line of the busy animation.

    sym: str symbol to write.

    prefix: str message to print to the left of sym.

    postfix: str message to print to the right of sym.

    num_chr_clear: int number of spaces to print to clear the previous line before printing the new line. 

    Returns: the number of characters printedm which is usually equal to: len(prefix + sym + postfix + '\r')

    As an example how to use this function, see busy_demo().
    '''
    if num_chr_clear>0:
        sys.stdout.write('%s\r' % (' '*num_chr_clear, ))
        sys.stdout.flush()
    
    line = '%s[%s]%s\r' % (prefix, sym, postfix)
    sys.stdout.write(line)
    sys.stdout.flush()
    return len(line)


import time

class SpeedoMeter:

    def __init__(self, label='counts'):
        self.t0 = None
        self.t1 = None
        self.prev_count = 0
        self.label = label
    
    def progress(self, count, total, prefix='', postfix='', num_chr_clear=0):
        '''Updates sys.stdout with the next line of the progress animation.

        count: int current share of the total prpgress.

        total: int maximum progress value.

        prefix: str message to print to the left of sym.

        postfix: str message to print to the right of sym.

        Returns: None

        As an example how to use this function, see progress_demo().
        '''
        self.t1 = time.monotonic()
        if self.t0 is not None and self.t1 > self.t0:
            speed = (count - self.prev_count) / (self.t1 - self.t0)
        else:
            speed = None
        self.t0 = self.t1
        self.prev_count = count
        
        if num_chr_clear>0:
            sys.stdout.write('%s\r' % (' '*num_chr_clear, ))
            sys.stdout.flush()

        bar_len = 60
        filled_len = int(round(bar_len * count / float(total)))

        percents = round(100.0 * count / float(total), 1)
        bar = '=' * filled_len + '-' * (bar_len - filled_len)

        line = '%s[%s] %s%s [speed: %s %s/s]%s\r' % (prefix, bar, percents, '%', ("%.3f" % speed) if speed is not None else "--", self.label, postfix)
        sys.stdout.write(line)
        sys.stdout.flush()
        return len(line)

        
def progress_demo():
    import time
    
    stages = [10, 20, 15, 30, 20, 0]
    total = sum(stages)
    cur = 0
    for a in stages:
        cur += a
        progress(cur, total, prefix="Progress: ", postfix=" (cur=%s)" % (a/10.0))
        time.sleep(a/10.0)
    sys.stdout.write("\n")


def busy_demo():
    import time    
    symbols = "*.. .*. ..* .*.".split(" ")
    stages = [5] * 20
    idx = 0
    n = 0
    for a in stages:
        n = busy(symbols[idx], prefix="Busy demo: ", postfix=' Ok' if idx % 4 != 0 else ' !!!!', num_chr_clear=n)
        idx +=1
        if idx>=len(symbols):
            idx = 0
        time.sleep(a/10.0)
    sys.stdout.write("\n")


def speed_demo(): 
    import time
    import random
    
    meter = SpeedoMeter(label='batches')
    
    stages = [10, 20, 15, 30, 20, 0]
    proc_times = [(random.random() + 0.5) * (s/10.0) for s in stages ]
    total = sum(stages)
    cur = 0
    n = 0
    n = meter.progress(0, total, prefix="Progress: ")#, postfix=" (cur=0)")    
    for a,d in zip(stages,proc_times):
        time.sleep(d)
        cur += a
        n = meter.progress(cur, total, prefix="Progress: ",
                           postfix=" (batch size=%s)" % a,
                           num_chr_clear=n)
    sys.stdout.write("\n")

    
if __name__=='__main__':
    #progress_demo()
    #busy_demo()
    speed_demo()
