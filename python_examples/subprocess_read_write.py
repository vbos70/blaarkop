from subprocess import Popen, PIPE
import gzip
import glob
import sys
import threading

# goal: Write to stdin of subprocesses and make an iterator of its stdout.
#       The subprocess takes a filename as input.
#       If the filename ends in .gz, the subprocess gunzips the file.
#       The subprocess writes the file content to its stdout.

inputfiles = glob.glob('random_bytes_50000Kb.*')

def open_stream(filename, mode='rb'):
    '''Opens filename in binary-read mode [default] en returns a fileobject.
    If filename ends in .gz, the file is opened with gzip.open(). Otherwise
    it is opened with open()'''
    if filename.endswith('.gz'):
        openfile = gzip.open
    else:
        openfile = open
    return openfile(filename, mode=mode)


# gen0 is a "solution" without subprocesses. It specifies the expected behaviour.
# gen0 yields from the fileobject directly. So, it is an generator.
def gen0(filename):
    with open_stream(filename) as instream:
        yield from instream

for filename in inputfiles:
    print(f"gen0:{filename}:{sum(len(b) for b in gen0(filename))}")

print()

# gen1 is a partial solution
# 1. it creates a subprocess that writes the file content to stdout
# 2. the subprocess yields from stdin. So, gen1 is a generator.
# 3. The subprocess stdin is set to the opened file.
#
# bug:
# 1. gen1 does not work for gzipped files.
# 2. it looks like the subprocess reads from the original (gzipped) file instead
# 3. of the un-gzipped file.
# 4. The un-gzipped file does not exist as a real file, just as a fileobject in
#    this script.
def gen1(filename):
    with open_stream(filename) as instream:
        p0 = Popen(["cat"], shell=False, stdin=instream, stdout=PIPE, stderr=sys.stderr, close_fds=False)
        yield from p0.stdout

for filename in inputfiles:
    print(f"gen1:{filename}:{sum(len(b) for b in gen1(filename))}")

print()

# gen2 is a working solution.
# 1. The subprocess reads from stdin and writes to stdout.
# 2. A separate Thread in this script writes the content of the file to
#    the subprocess' stdin.
# 3. gen2 "yields" from the subprocess' stdout. So, it is a generator.
def to_stdin(proc, instream):
    for b in instream:
        proc.stdin.write(b)
    proc.stdin.flush()
    proc.stdin.close()


def gen2(filename):
    with open_stream(filename) as instream:
        p0 = Popen(["cat"], shell=False, stdin=PIPE, stdout=PIPE, stderr=sys.stderr)
        rc = None
        try:
            t = threading.Thread(target=to_stdin, args=(p0, instream))
            t.start()

            yield from p0.stdout

            t.join()
            rc = p0.wait()
            if rc != 0:
                print(f"rc={rc}")
        finally:
            if rc is None:
                print('Killing subprocess p0')
                p0.kill()

for filename in inputfiles:
    print(f"gen2:{filename}:{sum(len(b) for b in gen2(filename))}")
