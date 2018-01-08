""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/deduction.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def inverse_mp(proof, assumption, print_as_proof_forms=False):
    """ Takes a proof, whose first six assumptions/axioms are Prover.AXIOMS, of
        a conclusion from a list of assumptions/axioms that contains the given
        assumption as a simple formula (i.e., without any templates), where no
        step of the proof is a UG step over a variable that is free in the
        given assumption, and returns a proof of (assumption−>conclusion) from
        the same assumptions except assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is str
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions[:len(Prover.AXIOMS)] == Prover.AXIOMS
    print('org proof assumptions:', proof.assumptions)
    print('our kilshon' , assumption)
    new_proof_assump = copy.deepcopy(proof.assumptions)
    del new_proof_assump[Schema(new_proof_assump.index(assumption))]
    new_proof = Proof(assumption, proof.conclusion, [])
    # divide to cases and run recurs
    for line in proof.lines:
        l_type = line.justification[0]
        if l_type == 'A':
            n
        elif l_type == 'T':
            pass
        elif l_type == 'MP':
            pass
        elif l_type == 'UG':
            pass

    # CASE1 line just is T    sol: T -> assumption -> T ; do MP and we get assumption -> T
    # CASE2 line just is A    solution1: A -> assumption -> A; do MP and we get assumption -> A (when A!=assumption)
                              #solution2: A == assumption -> ; add_tautology(assumption)
    # CASE3 line just is MP   solution: find assumption -> (A->B) , find assumption -> A in prev lines
                                        # use tau_inf to get assumption -> B
    # CASE4 line just is UG   solution: add UG  Ax[assumption -> cur] , when x is the same var used in org line
                                        # add US Ax[assumption -> cur] -> (assumption -> Ax[cur])
                                        # add MG to get assumption -> Ax[cur]

    # Task 11.1

def proof_by_contradiction(proof, assumption, print_as_proof_forms=False):
    """ Takes a proof, whose first six assumptions/axioms are Prover.AXIOMS, of
        a contradiction (a formula whose negation is a tautology)  a list of
        assumptions/axioms that contains the given assumption as a simple
        formula (i.e., without any templates), where no step of the proof is a
        UG step over a variable that is free in the given assumption, and
        returns a proof of ~assumption from the same assumptions except
        assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is str
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions[:len(Prover.AXIOMS)] == Prover.AXIOMS
    # Task 11.2
