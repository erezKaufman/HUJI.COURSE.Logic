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

    rules = [MP, I1, I2]  # create rules for the proof

    # create lines
    lines = []
    lines.append(DeductiveProof.Line(Formula.from_infix('((p->((p->p)->p))->((p->(p->p))->(p->p)))'), 2, []))
    lines.append(DeductiveProof.Line(Formula.from_infix('(p->(p->p))'), 1, []))
    lines.append(DeductiveProof.Line(Formula.from_infix('(p->((p->p)->p))'), 1, []))
    lines.append(DeductiveProof.Line(Formula.from_infix('((p->(p->p))->(p->p))'), 0, [2, 0]))
    lines.append(DeductiveProof.Line(Formula.from_infix('(p->p)'), 0, [1, 3]))
    dec = DeductiveProof(statement, rules, lines)
    return dec


def inverse_mp(proof: DeductiveProof, assumption: Formula):
    """ Return a valid deductive proof for '(assumption->conclusion)', where
        conclusion is the conclusion of proof, from the assumptions of proof
        except assumption, via MP,I1,I2 """
    new_statement = InferenceRule([a for a in proof.statement.assumptions if a != assumption],
                                  Formula(IMPLICATION_OPERATOR, assumption, proof.statement.conclusion))

    new_proof_lines = []


    task_1_Formula = Formula(IMPLICATION_OPERATOR, assumption, assumption)  # create 'A->A' formula
    assumption_inference = InferenceRule([], task_1_Formula)
    for line_index, line in enumerate(proof.lines):
        line_instance = proof.instance_for_line(line_index)  # returns the current line as an inference rule
        # case 1 - if the assumption(A) is in the line

        if line.conclusion == assumption:
            pivot_index = len(new_proof_lines)
            task_1_proof = prove_implies_self()  # proves 'p->p'

            assumption_proof_with_task_1 = prove_instance(task_1_proof, assumption_inference)
            for assumption_index, assumption_line in enumerate(assumption_proof_with_task_1.lines):
                justification_list = []
                if assumption_line.justification:
                    justification_list = [a + pivot_index for a in assumption_line.justification]

                new_proof_lines.append(
                    DeductiveProof.Line(assumption_line.conclusion, assumption_line.rule, justification_list))

        # case 3 - if there is an MP line
        elif line.rule == 0:
            old_justification_list = []
            # I now find the use of p and p->q in the MP call
            for justification in line.justification:
                old_justification_list.append(proof.lines[justification].conclusion)
            p = assumption
            q = old_justification_list[0]
            r = old_justification_list[1].second
            # create the first part of I2 proof
            line_1_first = Formula(IMPLICATION_OPERATOR, p, Formula(IMPLICATION_OPERATOR, q, r))
            # create the second part of I2 proof
            line_1_second = Formula(IMPLICATION_OPERATOR, Formula(IMPLICATION_OPERATOR, p, q),
                                    Formula(IMPLICATION_OPERATOR, p, r))

            line_1_formula = Formula(IMPLICATION_OPERATOR, line_1_first, line_1_second)
            new_proof_lines.append(DeductiveProof.Line(line_1_formula, 2, []))
            # create l2 where I prove MP with previous lines
            mp_p_justification = -1
            # search for the  'p' part of the proof - that will be line_1_first.
            for temp_line_index, temp_line in enumerate(new_proof_lines):
                if temp_line.conclusion == line_1_first:
                    mp_p_justification = temp_line_index
            # add l2 as an MP proof
            new_proof_lines.append(DeductiveProof.Line(line_1_second, 0, [mp_p_justification, len(new_proof_lines)-1]))
            mp_p_justification = -2
            # search for the 'p' part of the proof - that will be line_1_second.first
            for temp_line_index, temp_line in enumerate(new_proof_lines):
                if temp_line.conclusion == line_1_second.first:
                    mp_p_justification = temp_line_index
            new_proof_lines.append(DeductiveProof.Line(line_1_second.second, 0, [mp_p_justification,
                                                                                 len(new_proof_lines)-1]))


        # case 2 - if there is another assumption in the line
        # else it's another rule or assumption, we would like to prove it in a way that the conclusion of this
        # line will be proven by 'assumption -> conclusion'
        else:
            new_proof_lines.append(
                DeductiveProof.Line(line.conclusion, line.rule, line.justification))  # add the line as itself (l1)
            assumption_implies_formula = Formula(IMPLICATION_OPERATOR, assumption, line.conclusion)
            line_2_formula = Formula(IMPLICATION_OPERATOR, line.conclusion, assumption_implies_formula)

            new_proof_lines.append(DeductiveProof.Line(line_2_formula, 1, []))  # add line 2 (l2)
            # this will be line 3 (l3). we will prove this by MP using l1 and l2
            line_3_formula = assumption_implies_formula
            new_proof_lines.append(
                DeductiveProof.Line(line_3_formula, 0, [len(new_proof_lines)-2, len(new_proof_lines)-1]))


    return DeductiveProof(new_statement, proof.rules, new_proof_lines)


@lru_cache(maxsize=1)  # Cache the return value of prove_hypothetical_syllogism
def prove_hypothetical_syllogism():
    """ Return a valid deductive proof for '(p->r)' from the assumptions
        '(p->q)' and '(q->r)' via MP,I1,I2 """
    assumptions = [Formula(IMPLICATION_OPERATOR, 'p', 'q'), Formula(IMPLICATION_OPERATOR, 'q', 'r')]
    conclusion = Formula(IMPLICATION_OPERATOR,'p','r')
    statement = InferenceRule(assumptions,conclusion )

    # test_proof = DeductiveProof(Formula('r'),[MP,I1,I2],)

    # I1 = InferenceRule([], Formula.from_infix('(p->(q->p))'))
    # I2 = InferenceRule([], Formula.from_infix('((p->(q->r))->((p->q)->(p->r)))'))

