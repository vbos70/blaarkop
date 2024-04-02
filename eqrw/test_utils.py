from utils import *
from test_framework import test, run_tests, test_summary, test_print

@test
def test_unique():
    assert list(unique([5,3,4,4,3,1,5])) == [5,3,4,1]
    for l in [list(range(100)) , [5,3,4,4,3,1,5], []]:
        l = list(range(100))
        assert l == list(unique(l))
        l2 = l + l
        assert len(list(unique(l2))) == len(l)
        assert l == list(unique(l2))

if __name__ == '__main__':
    run_tests(print_summary_only=True, new_suppress_test_output=False)
    print(test_summary())

