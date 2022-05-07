# The progress() function is from:
#     https://gist.github.com/vladignatyev/06860ec2040cb497f0f3
import sys


def progress(count, total, status=''):
    bar_len = 60
    filled_len = int(round(bar_len * count / float(total)))

    percents = round(100.0 * count / float(total), 1)
    bar = '=' * filled_len + '-' * (bar_len - filled_len)

    sys.stdout.write('[%s] %s%s ...%s\r' % (bar, percents, '%', status))
    sys.stdout.flush()  # As suggested by Rom Ruben (see: http://stackoverflow.com/questions/3173320/text-progress-bar-in-the-console/27871113#comment50529068_27871113)

    
def progress_demo():
    import time
    
    stages = [10, 20, 15, 30, 20, 0]
    total = sum(stages)
    cur = 0
    for a in stages:
        cur += a
        progress(cur, total, status=a)
        time.sleep(a/10.0)
    sys.stdout.write("\n")
    
if __name__=='__main__':
    progress_demo()
    
