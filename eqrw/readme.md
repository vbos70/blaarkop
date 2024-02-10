# EQRW: equational rewriting

A tool to write equational proofs.

## Requirements

1. Python3 (tested with python 3.10.12)
2. z3

## Python Environment

Setup:

    python -m venv pyenv
    source pyenv/bin/activate
    pip install z3-solver


## Features

1. Create equational proofs
2. Terms/expressions are z3 terms
3. Extend proofs: proof1 += t, eqs
   succeeds if z3's solver can derives t from the current state by using equations in eqs.
4. Combine proofs: proof1 += proof2
   succeeds is last term of proof1 is equal to first term of proof2

   
## TODO

1. Sub-proofs
   proof.add_subproof(subp, t):
   - subp.theorem() is used to prove t from current point in proof
   - subp is a Proof
   - t is a (z3) term
   
   1. If any subproof is incomplete, also the proof itself is incomplete.
   2. The proof's summary should list the number of sub-proofs and the number of incomplete
      sub-proofs.
   3. The __str__() of Proof shall also print sub-proofs (indented)

2. Verify
   Re-run all steps and returns False is at least one fails
   1. Remove invalid steps
      replaces invalid steps by incomplete sub-proofs 
   Possibly add "miracle" as a step to prove anything.

3. Add __getitem__ and slices to proofs
   p[0:4] returns the Proof from term 0 to term 3 of this Proof.

4. List unproven steps with index
   The index can be used in __getitem__ and slices.
