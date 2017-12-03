""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/provers.py """

from functools import lru_cache

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

    for line_index, line in enumerate(proof.lines):
        # case 1 - if the assumption(A) is in the line

        if line.conclusion == assumption:
            check_if_THE_assumption(assumption, new_proof_lines)

        elif line.rule == 0:  # case 3 - if there is an MP line
            check_if_MP(assumption, line, new_proof_lines, proof)


        # case 2 - if there is another assumption in the line
        # else it's another rule or assumption, we would like to prove it in a way that the conclusion of this
        # line will be proven by 'assumption -> conclusion'
        else:
            cheack_assumptions(assumption, line, new_proof_lines)
    return DeductiveProof(new_statement, proof.rules, new_proof_lines)


def check_if_THE_assumption(assumption: Formula, new_proof_lines: list):
    """
    help method to work when the assumption at hand appears in the proof
    :param assumption:  the assumption to be treated
    :param new_proof_lines: a list of new lines
    """
    task_1_Formula = Formula(IMPLICATION_OPERATOR, assumption, assumption)  # create 'A->A' formula
    assumption_inference = InferenceRule([], task_1_Formula)
    pivot_index = len(new_proof_lines)
    task_1_proof = prove_implies_self()  # proves 'p->p'
    assumption_proof_with_task_1 = prove_instance(task_1_proof, assumption_inference)
    for assumption_index, assumption_line in enumerate(assumption_proof_with_task_1.lines):
        justification_list = []
        if assumption_line.justification:
            justification_list = [a + pivot_index for a in assumption_line.justification]

        new_proof_lines.append(
            DeductiveProof.Line(assumption_line.conclusion, assumption_line.rule, justification_list))


def check_if_MP(assumption, line, new_proof_lines, proof):
    """
    help method to work on a line that usses the rul of MP
    :param assumption:  the assumption to be treated
    :param line: the original line
    :param new_proof_lines:  the list of new lines
    :param proof: the original proog
    """
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
    for temp_line_index in range(len(new_proof_lines)-1,0,-1):
        if new_proof_lines[temp_line_index].conclusion == line_1_first:
            mp_p_justification = temp_line_index
            break

    # add l2 as an MP proof
    new_proof_lines.append(
        DeductiveProof.Line(line_1_second, 0, [mp_p_justification, len(new_proof_lines) - 1]))
    mp_p_justification = -2
    # search for the 'p' part of the proof - that will be line_1_second.first
    for  temp_line_index in range(len(new_proof_lines)-1,0,-1):
        if new_proof_lines[temp_line_index].conclusion == line_1_second.first:
            mp_p_justification = temp_line_index
            break
    new_proof_lines.append(DeductiveProof.Line(line_1_second.second, 0, [mp_p_justification,
                                                                         len(new_proof_lines) - 1]))


def cheack_assumptions(assumption, line, new_proof_lines):
    """
    help method to work on lines containing any kind of assumption that is not MP
    :param assumption: the assumption to be treated
    :param line:  the original line
    :param new_proof_lines:  new line list
    """
    new_proof_lines.append(
        DeductiveProof.Line(line.conclusion, line.rule, line.justification))  # add the line as itself (l1)
    assumption_implies_formula = Formula(IMPLICATION_OPERATOR, assumption, line.conclusion)
    line_2_formula = Formula(IMPLICATION_OPERATOR, line.conclusion, assumption_implies_formula)
    new_proof_lines.append(DeductiveProof.Line(line_2_formula, 1, []))  # add line 2 (l2)
    # this will be line 3 (l3). we will prove this by MP using l1 and l2
    line_3_formula = assumption_implies_formula
    new_proof_lines.append(
        DeductiveProof.Line(line_3_formula, 0, [len(new_proof_lines) - 2, len(new_proof_lines) - 1]))


@lru_cache(maxsize=1)  # Cache the return value of prove_hypothetical_syllogism
def prove_hypothetical_syllogism():
    """ Return a valid deductive proof for '(p->r)' from the assumptions
        '(p->q)' and '(q->r)' via MP,I1,I2 """
    assumptions = [Formula(IMPLICATION_OPERATOR, Formula('p'), Formula('q')), Formula(IMPLICATION_OPERATOR,
                                                                  Formula('q'), Formula('r')), Formula('p')]
    rules = [MP, I1, I2]
    lines = []
    conclusion = Formula('r')
    statement = InferenceRule(assumptions, conclusion)
    # temp_statement =
    lines.append(DeductiveProof.Line(Formula('p')))
    lines.append(DeductiveProof.Line(assumptions[0]))
    lines.append(DeductiveProof.Line(assumptions[1]))
    lines.append(DeductiveProof.Line(Formula('q'), 0, [0, 1]))
    lines.append(DeductiveProof.Line(Formula('r'), 0, [3, 2]))
    proof = DeductiveProof(statement, rules, lines)
    return_proof = inverse_mp(proof, Formula('p'))
    print(return_proof)

    return return_proof
