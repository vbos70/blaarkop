from traceback import print_exception

num_tests = 0
num_failed_tests = 0
test_output = []
suppress_test_output = False
summary_only = False
test_dict = dict()

def test_print(*args):
    global suppress_test_output
    if not suppress_test_output:
        test_output.extend(list(str(a) for a in args))

def test(func):
    global test_dict

    def inner():
        global num_tests
        global num_failed_tests
        global test_output
        global summary_only

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

    if func.__module__ is not None and len(func.__module__)>0:
        tn = f'{func.__module__}.py:{func.__name__}()'
    else:
        tn = f':{func.__name__}()'
    if tn in test_dict:
        print(f'Error: duplicate test name: {tn}')
    test_dict[tn] = inner
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
    global test_dict
    global summary_only

    # remember global output suppression switch
    sto = suppress_test_output
    so = summary_only

    suppress_test_output = new_suppress_test_output
    summary_only = print_summary_only

    num_tests = 0
    num_failed_tests = 0

    tf_iter = test_dict
    if len(selected) > 0:
        tf_iter = (tf for tf in test_dict if test_dict[tf] in selected)

    for tf in tf_iter:
        if not summary_only:
            print(f'# {tf}: ', end='', flush=True)
        test_dict[tf]()

    # restore global output suppression
    suppress_test_output = sto
    summary_only = so
