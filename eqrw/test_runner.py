from test_framework import run_tests, test_summary

import test_utils
import test_eqrw
import test_equation
import test_theory
import test_eqproof
import test_T1_eqt
import test_T2_eqt
import test_process
import test_process_theory
import test_pyspec
import test_prover

if __name__ == '__main__':

    run_tests(new_suppress_test_output=True)
    #run_tests(print_summary_only=True, new_suppress_test_output=True)
    print(test_summary())
