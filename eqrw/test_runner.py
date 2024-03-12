from test_framework import run_tests, set_test_suite, test_summary
set_test_suite('eqrw')
import test_eqrw

set_test_suite('test_equation')
import test_equation

set_test_suite('test_theory')
import test_theory

set_test_suite('test_eqproof')
import test_eqproof

set_test_suite('test_T1_eqt')
import test_T1_eqt

set_test_suite('test_T2_eqt')
import test_T2_eqt

if __name__ == '__main__':

    run_tests(new_suppress_test_output=True)
    #run_tests(print_summary_only=True, new_suppress_test_output=True)
    print(test_summary())
