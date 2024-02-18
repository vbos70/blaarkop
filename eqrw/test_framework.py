from traceback import print_exception

num_tests = 0
num_failed_tests = 0
test_output = []
suppress_test_output = False
summary_only = False
test_funcs = []

def test_print(*args):
    global suppress_test_output
    if not suppress_test_output:
        test_output.extend(list(str(a) for a in args))

def test(func):
    global test_funcs

    def inner():
        global num_tests
        global num_failed_tests
        global test_output
        global summary_only

        if not summary_only:
            print(f'# Test {func.__name__}: ', end='', flush=True)
        try:            
            test_output = []
            num_tests += 1
            func()
            if not summary_only:
                print(f'passed.')
            if len(test_output)>0:
                print("Test output:\n" + "\n".join(test_output))
        except AssertionError as ae:
            num_failed_tests += 1
            print(f'Failed:')
            print_exception(ae, limit=-1)
        except Exception as e:
            num_failed_tests += 1
            print(f'Error:')
            print_exception(e)

    test_funcs.append(inner)
    return inner

def test_summary():
    global num_tests
    global num_failed_tests
    result = [f'# SUMMARY:{num_tests} tests']
    if num_failed_tests > 0:
        result.append(f':{num_tests-num_failed_tests} passed:{num_failed_tests} failed.')
    else:
        result.append(':all passed.')
    return "".join(result)


def run_tests(*selected, print_summary_only=False, new_suppress_test_output = False):
    global num_tests
    global num_failed_tests
    global suppress_test_output
    global test_funcs
    global summary_only

    # remember global output suppression switch
    sto = suppress_test_output
    so = summary_only

    suppress_test_output = new_suppress_test_output
    summary_only = print_summary_only

    num_tests = 0
    num_failed_tests = 0

    tf_iter = test_funcs
    if len(selected) > 0:
        tf_iter = (tf for tf in test_funcs if tf in selected)

    for tf in tf_iter:
        tf()

    # restore global output suppression
    suppress_test_output = sto
    summary_only = so
