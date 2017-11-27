""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/tautology.py """

from propositions.syntax import *
from propositions.proofs import *
from propositions.provers import MP,I1,I2,inverse_mp
from propositions.semantics import *

# Axiomatic Inference Rules (MP, I1, and I2 are imported from provers.py)
I3 = InferenceRule([], Formula.from_infix('(~p->(p->q))'))
NI = InferenceRule([], Formula.from_infix('(p->(~q->~(p->q)))'))

NN = InferenceRule([], Formula.from_infix('(p->~~p)'))

R = InferenceRule([], Formula.from_infix('((q->p)->((~q->p)->p))'))

AXIOMATIC_SYSTEM_IMPLIES_NOT = [MP, I1, I2, I3, NI, NN, R]

A = InferenceRule([], Formula.from_infix('(p->(q->(p&q)))'))
NA1 = InferenceRule([], Formula.from_infix('(~p->~(p&q))'))
NA2 = InferenceRule([], Formula.from_infix('(~q->~(p&q))'))

O1 = InferenceRule([], Formula.from_infix('(p->(p|q))'))
O2 = InferenceRule([], Formula.from_infix('(q->(p|q))'))

NO = InferenceRule([], Formula.from_infix('(~p->(~q->~(p|q)))'))

T  = InferenceRule([], Formula.from_infix('T'))

NF  = InferenceRule([], Formula.from_infix('~F'))

AXIOMATIC_SYSTEM = [MP, I1, I2, I3, NI, NN, A, NA1, NA2, O1, O2, NO, T, NF, R]

def find_index_by_conclusion(conclusion, lines):
    for index, line in enumerate(lines):
        if line.conclusion == conclusion:
            return index

def prove_in_model_implies_not(formula, model):
    def prove_in_model_implies_not_helper(formula:formula, model:dict):
        # just var
        if is_variable(formula.root):
            return formula

        # (psi -> psi)
        elif is_binary(formula.root): # root is ->
            p = prove_in_model_implies_not_helper(formula.first, model)
            q = prove_in_model_implies_not_helper(formula.second, model)

            if evaluate(formula.first, model) is False: #psi_1 is not true in M
                not_p = Formula('~', p)
                l3 = Formula('->' , not_p, Formula('->', p, q))
                lines.append(DeductiveProof.Line(l3, 3, [])) # from I3
                l2 = Formula('->', p, q)  # build psi_1->psi_2
                lines.append(DeductiveProof.Line(l2, 0, [find_index_by_conclusion(not_p, lines), len(lines) - 1]))  # from I2
                return l2

            elif evaluate(formula.second, model) is True: # psi_2 is True in M
                l1 = Formula('->', q, Formula('->', p, q)) # build I1
                lines.append(DeductiveProof.Line(l1, 1, [])) # from I1
                l2 = Formula('->', p, q) #build psi_1->psi_2
                lines.append(DeductiveProof.Line(l2, 0, [find_index_by_conclusion(q, lines) ,len(lines)-1])) # from I2
                return l2

            else:
                print('OOOMMMMGGGGGGGG , wrong input or somthing went wrong with recurtion')
                exit(-1)
                return


        # elif is_unary(formula.root) and not is_variable(formula.first.root): # TODO why do we check here if formula.first.root is var?
        elif is_unary(formula.root): # TODO why do we check here if formula.first.root is var?
            if is_unary(formula.first.root):  # the next root is ~
                p = prove_in_model_implies_not_helper(formula.first.first, model)
                line_1_to_add = Formula(NEGATE_OPERATOR, Formula(NEGATE_OPERATOR, p))
                p_index = dummy_index = -1
                p_index ,dummy_index = find_index(p,p_index,line_1_to_add.first,dummy_index)
                NN_line = Formula(IMPLICATION_OPERATOR,p,line_1_to_add)

                lines.append(DeductiveProof.Line(NN_line, 5, []))

                MP_line = NN_line.second

                lines.append(DeductiveProof.Line(MP_line,0,[p_index,len(lines)-1]))

                return MP_line

            elif is_variable(formula.first.root):
                return Formula('~', prove_in_model_implies_not_helper(formula.first, model))

            else: # we have ~ and psi, deal with NI
                # if is_variable(formula.first.first) and is_variable(formula.first.second):
                #     pass
                # elif is_variable(formula.first.first) and not is_variable(formula.first.second):
                #     pass
                # elif not is_variable(formula.first.first) and is_variable(formula.first.second):
                #     pass
                #

                p = prove_in_model_implies_not_helper(formula.first.first, model)

                q = prove_in_model_implies_not_helper(formula.first.second,model)
                q = Formula(NEGATE_OPERATOR,q)

                p_implie_q = Formula(IMPLICATION_OPERATOR, p, q)

                implie1 = Formula(NEGATE_OPERATOR, p_implie_q)

                n_q = Formula(NEGATE_OPERATOR, q)

                implie_2 = Formula(IMPLICATION_OPERATOR, n_q, implie1)

                f1 = Formula(IMPLICATION_OPERATOR, p, implie_2)


                # add the first line for the specific proof. I add NI here
                lines.append(DeductiveProof.Line(f1, 4,[]))
                # I run on all the lines and search for 'p' to proof the line with MP
                # I know that p and ~q must appear as an assumption in the lines of the proof
                p_index = -1
                q_index = -2
                p_index, q_index = find_index(p, p_index, q, q_index)
                if p_index ==-1 or q_index == -2:
                    print("bad index, p is: {}, q is: {}".format(p,q))
                    exit(-1)
                ni_part_2 = implie_2
                # add line 2 as an MP conclusion for
                lines.append(DeductiveProof.Line(ni_part_2, 0, [p_index, len(lines) - 1]))
                mp_part_2 = ni_part_2.second
                lines.append(DeductiveProof.Line(mp_part_2, 0, [q_index, len(lines) - 1]))
                return mp_part_2





    def find_index(p, p_index, q, q_index):
        for line_index, line in enumerate(lines):
            if line.conclusion == p:
                p_index = line_index
                if p == q:
                    break
            elif line.conclusion == q:
                q_index = line_index
        return p_index, q_index

    """ Return a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT from the
        assumptions that all variables are valued as in model, with the
        assumptions being ordered alphabetically by the names of the variables.
        It is assumed that formula is true in model, and may only have the
        operators implies and not in it """
    variables = sorted(list(formula.variables()))
    assumptions = []
    for var in variables:
        if model[var] is True:
            assumptions.append(Formula(var))
        else: assumptions.append(Formula('~', Formula(var)))


    statement = InferenceRule(assumptions, formula)
    lines = [DeductiveProof.Line(ass, None, None) for ass in assumptions]
    prove_in_model_implies_not_helper(formula,model)
    return DeductiveProof(statement, AXIOMATIC_SYSTEM_IMPLIES_NOT, lines)





    # Task 6.1

def reduce_assumption(proof_true, proof_false):
    """ Return a proof of the same formula that is proved in both proof_true
        and proof_false, via the same inference rules used in both proof_true
        and proof_false, from the assumptions common to proof_true and
        proof_false. The first three of the inference rules in the given proofs
        are assumed to be M,I1,I2, any additional inference rules are assumed
        to have no assumptions, the inference rules in the given proofs are
        assumed to contain R, and the assumptions of both proofs are assumed to
        coincide, except for the last assumption, where that of proof_false is
        the negation of that of proof_true """
    # Task 6.2

def proof_or_counterexample_implies_not(formula):
    """ Return either a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT, or a
        model where formula does not hold. It is assumed that formula may only
        have the operators implies and not in it """
    # Task 6.3

def prove_in_model(formula, model):
    """ Return a proof of formula via AXIOMATIC_SYSTEM from the assumptions
        that all variables are valued as in model, with the assumptions being
        ordered alphabetically by the names of the variables. It is assumed
        that formula is true in model """
    # Task 6.4

def proof_or_counterexample(formula):
    """ Return either a proof of formula via AXIOMATIC_SYSTEM, or a model where
        formula does not hold """
    # Task 6.5

def proof_or_counterexample_for_inference(rule):
    """ Return either a proof of rule via AXIOMATIC_SYSTEM, or a model where
        rule does not hold """
    # Task 6.6

def model_or_inconsistent(formulae):
    """ Return either a model where all of formulae hold, or a list of two
        proofs, both from formulae via AXIOMATIC_SYSTEM, the first of some
        formula and the second of the negation of the same formula """
    # Task 6.7

if __name__ == '__main__':
    pass


