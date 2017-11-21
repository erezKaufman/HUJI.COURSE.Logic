""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/provers.py """

from functools import lru_cache

from propositions.syntax import *
from propositions.proofs import *

# Tautological Inference Rules
MP = InferenceRule([Formula.from_infix('p'), Formula.from_infix('(p->q)')],
                   Formula.from_infix('q'))

I1 = InferenceRule([], Formula.from_infix('(p->(q->p))'))
I2 = InferenceRule([], Formula.from_infix('((p->(q->r))->((p->q)->(p->r)))'))
# I2 = InferenceRule([], Formula.from_infix('((p->(q->r))->((p->q)->(p->r)))'))

N = InferenceRule([], Formula.from_infix('((~p->~q)->(q->p))'))

A1 = InferenceRule([], Formula.from_infix('(p->(q->(p&q)))'))
A2 = InferenceRule([], Formula.from_infix('((p&q)->p)'))
A3 = InferenceRule([], Formula.from_infix('((p&q)->q)'))

O1 = InferenceRule([], Formula.from_infix('(p->(p|q))'))
O2 = InferenceRule([], Formula.from_infix('(q->(p|q))'))
O3 = InferenceRule([], Formula.from_infix('((p->r)->((q->r)->((p|q)->r)))'))

T = InferenceRule([], Formula.from_infix('T'))

F = InferenceRule([], Formula.from_infix('~F'))

AXIOMATIC_SYSTEM = [MP, I1, I2, N, A1, A2, A3, O1, O2, O3, T, F]


@lru_cache(maxsize=1)  # Cache the return value of prove_implies_self
def prove_implies_self():
    """ Return a valid deductive proof for '(p->p)' via MP,I1,I2 """
    # i1_with_assumptions = InferenceRule([I1.conclusion.first],I1.conclusion.second)
    # i2_with_assumptions = InferenceRule([I2.conclusion.first,I2.conclusion.second.first],I2.conclusion.second.second)

    statement = InferenceRule([], Formula.from_infix('(p->p)'))  # create conclusion

    rules = [I1, I2, MP]  # create rules for the proof

    # create lines
    lines = []
    lines.append(DeductiveProof.Line(Formula.from_infix('((p->((p->p)->p))->((p->(p->p))->(p->p)))'), 1, []))
    lines.append(DeductiveProof.Line(Formula.from_infix('(p->(p->p))'), 0, []))
    lines.append(DeductiveProof.Line(Formula.from_infix('(p->((p->p)->p))'), 0, []))
    lines.append(DeductiveProof.Line(Formula.from_infix('((p->(p->p))->(p->p))'), 2, [2, 0]))
    lines.append(DeductiveProof.Line(Formula.from_infix('(p->p)'), 2, [1, 3]))
    dec = DeductiveProof(statement, rules, lines)
    print(dec)
    return dec


def inverse_mp(proof, assumption):
    """ Return a valid deductive proof for '(assumption->conclusion)', where
        conclusion is the conclusion of proof, from the assumptions of proof
        except assumption, via MP,I1,I2 """
    # Task 5.3


@lru_cache(maxsize=1)  # Cache the return value of prove_hypothetical_syllogism
def prove_hypothetical_syllogism():
    """ Return a valid deductive proof for '(p->r)' from the assumptions
        '(p->q)' and '(q->r)' via MP,I1,I2 """
    # Task 5.4
