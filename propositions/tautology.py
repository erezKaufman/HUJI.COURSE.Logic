""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/tautology.py """

from propositions.syntax import *
from propositions.proofs import *
from propositions.provers import MP, I1, I2, inverse_mp
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

T = InferenceRule([], Formula.from_infix('T'))

NF = InferenceRule([], Formula.from_infix('~F'))

AXIOMATIC_SYSTEM = [MP, I1, I2, I3, NI, NN, A, NA1, NA2, O1, O2, NO, T, NF, R]
AXIOMATIC_DICT = {'MP': 0, 'I1': 1, 'I2': 2, 'I3': 3, 'NI': 4, 'NN': 5, 'A': 6, 'NA1': 7, 'NA2': 8, 'O1': 9, 'O2': 10,
                  'T': 11, 'NF': 12, 'R': 13}


def find_index_by_conclusion(conclusion, lines):
    for index, line in enumerate(lines):
        if line.conclusion == conclusion:
            return index
    return None


def prove_in_model_implies_not(formula, model):
    def prove_in_model_implies_not_helper(formula: formula, model: dict):
        # just var
        if is_variable(formula.root):
            return formula

        # (psi -> psi)
        elif is_binary(formula.root):  # root is ->
            if evaluate(formula.first, model) is False:  # psi_1 is not true in M
                not_p = prove_in_model_implies_not_helper(Formula('~', formula.first), model)
                l3 = Formula('->', not_p, formula)
                lines.append(DeductiveProof.Line(l3, 3, []))  # from I3
                # l2 = Formula('->', p, q)  # build psi_1->psi_2
                not_p_index = find_index_by_conclusion(not_p, lines)
                # if not_p_index is None:
                # print('we got a not found conclusion:' , not_p_index, 'for conclusion:', not_p)
                # exit(-1)
                lines.append(DeductiveProof.Line(formula, 0, [not_p_index, len(lines) - 1]))  # from I2
                return formula

            elif evaluate(formula.second, model) is True:  # psi_2 is True in M
                p = prove_in_model_implies_not_helper(formula.first, model)
                q = prove_in_model_implies_not_helper(formula.second, model)
                l1 = Formula('->', q, Formula('->', p, q))  # build I1
                lines.append(DeductiveProof.Line(l1, 1, []))  # from I1
                l2 = Formula('->', p, q)  # build psi_1->psi_2
                find_q_index = find_index_by_conclusion(q, lines)
                lines.append(DeductiveProof.Line(l2, 0, [find_q_index, len(lines) - 1]))  # from I2
                return l2

            else:
                print('OOOMMMMGGGGGGGG , wrong input or somthing went wrong with recurtion')
                exit(-1)
                return


        # elif is_unary(formula.root) and not is_variable(formula.first.root): #
        elif is_unary(formula.root):
            if is_unary(formula.first.root):  # the next root is ~
                p = prove_in_model_implies_not_helper(formula.first.first, model)
                line_1_to_add = Formula(NEGATE_OPERATOR, Formula(NEGATE_OPERATOR, p))
                p_index = find_index_by_conclusion(p, lines)
                NN_line = Formula(IMPLICATION_OPERATOR, p, line_1_to_add)
                lines.append(DeductiveProof.Line(NN_line, 5, []))
                MP_line = NN_line.second
                lines.append(DeductiveProof.Line(MP_line, 0, [p_index, len(lines) - 1]))
                return MP_line

            elif is_variable(formula.first.root):
                return Formula('~', prove_in_model_implies_not_helper(formula.first, model))

            else:  # we have ~ and psi, deal with NI
                p = prove_in_model_implies_not_helper(formula.first.first, model)  # ps1_1
                not_q = prove_in_model_implies_not_helper(Formula('~', formula.first.second), model)  # not_psi_2
                part_2 = Formula('->', not_q, formula)  # (~psi2 -> ~(psi_1 -> psi_2))
                ni = Formula('->', p, part_2)  # (psi_1 -> (~psi2 -> ~(psi_1 -> psi_2)))
                lines.append(DeductiveProof.Line(ni, 4, []))
                # I run on all the lines and search for 'p' to proof the line with MP
                # I know that p and ~q must appear as an assumption in the lines of the proof
                p_index = -1
                q_index = -2
                p_index, q_index = find_index(p, p_index, not_q, q_index)
                # if p_index == -1 or q_index == -2:
                #     print("bad index, p is: {}, q is: {}".format(p, not_q))
                #     exit(-1)
                # add line 2 as an MP conclusion for
                lines.append(DeductiveProof.Line(part_2, 0, [p_index, len(lines) - 1]))
                lines.append(DeductiveProof.Line(formula, 0, [q_index, len(lines) - 1]))
                return formula

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
        else:
            assumptions.append(Formula('~', Formula(var)))

    statement = InferenceRule(assumptions, formula)
    lines = [DeductiveProof.Line(ass, None, None) for ass in assumptions]
    prove_in_model_implies_not_helper(formula, model)
    return DeductiveProof(statement, AXIOMATIC_SYSTEM_IMPLIES_NOT, lines)


    # Task 6.1


# def create_not_not_asses(lines):
#     ret = []
#     for line in lines:
#         line_1_to_add = Formula(NEGATE_OPERATOR, Formula(NEGATE_OPERATOR, line.conclusion))
#         p_index = find_index_by_conclusion(line.conclusion, lines)
#         NN_line = Formula(IMPLICATION_OPERATOR, line.conclusion, line_1_to_add)
#         ret.append(DeductiveProof.Line(NN_line, 5, []))
#         MP_line = NN_line.second
#         ret.append(DeductiveProof.Line(MP_line, 0, [p_index, len(ret) + len(lines) - 1]))
#
#     return ret




def reduce_assumption(proof_true: DeductiveProof, proof_false: DeductiveProof):
    """ Return a proof of the same formula that is proved in both proof_true
        and proof_false, via the same inference rules used in both proof_true
        and proof_false, from the assumptions common to proof_true and
        proof_false. The first three of the inference rules in the given proofs
        are assumed to be M,I1,I2, any additional inference rules are assumed
        to have no assumptions, the inference rules in the given proofs are
        assumed to contain R, and the assumptions of both proofs are assumed to
        coincide, except for the last assumption, where that of proof_false is
        the negation of that of proof_true """

    new_lines = [] # init the list of new lines for the proof
    part_1_mp_index = -1
    part_2_mp_index = -2
    ######### do inverse_mp to the true proof ############
    last_true_assumption = proof_true.statement.assumptions[len(proof_true.statement.assumptions) - 1]
    inverse_proof_true = inverse_mp(proof_true, last_true_assumption)
    ######### finished inverse_mp ############



    ######### initiated statement for the new proof ############
    new_assumption = inverse_proof_true.statement.assumptions
    new_conclusion = proof_true.statement.conclusion
    new_statement = InferenceRule(new_assumption, new_conclusion)
    ######### finish init statement ############

    new_lines += inverse_proof_true.lines #  added lines of the first true proof
    part_1_mp_index = len(new_lines)-1 # get the line index for the true proof's conclusion
    ######### do inverse_mp to the false proof ############
    last_false_assumption = proof_false.statement.assumptions[len(proof_false.statement.assumptions) - 1]
    inverse_proof_false = inverse_mp(proof_false, last_false_assumption)
    ######### finished inverse_mp ############

    ######### adding line of the false proof, while changing the line numbers according to the new proof############
    current_new_line_index = len(new_lines)
    for line_index, line in enumerate(inverse_proof_false.lines):
        new_justification = None
        if line.justification is not None:
            new_justification = [a + current_new_line_index for a in line.justification]

        new_lines.append(DeductiveProof.Line(line.conclusion, line.rule, new_justification))
    ######### finish adding line of false proof ############

    part_2_mp_index = len(new_lines)-1 # get the line index for the false proof's conclusion

    # search for the lines in the proof where we get the conclusion

    # for line_index, line in enumerate(new_lines):
    #     if line.conclusion == inverse_proof_true.statement.conclusion:
    #         part_1_mp_index = line_index
    #     elif line.conclusion == inverse_proof_false.statement.conclusion:
    #         part_2_mp_index = line_index

            # TODO need to search for the conclusion of proof 1 and 2 , and use them with MP
            # we want to assume R, and with those two results above us we want to prove MP twice and get p (final conclusion)
    # first MP to isolate ((~q->p)->p) from R
    # ((q->p)->((~q->p)->p))
    p = proof_true.statement.conclusion
    q = last_true_assumption
    R_line = Formula(IMPLICATION_OPERATOR,Formula(IMPLICATION_OPERATOR,q,p),Formula(IMPLICATION_OPERATOR,
                                                                                    Formula(IMPLICATION_OPERATOR,
                                                                                            Formula(NEGATE_OPERATOR,
                                                                                                    q),p),p))
    # need to search for the rule number for R ...
    R_rule_index = -3
    for rule_index, rule in enumerate(proof_true.rules):
        if rule == R:
            R_rule_index = rule_index
            break

    new_lines.append(DeductiveProof.Line(R_line,R_rule_index,[])) # added R line

    first_mp_conclusion = R_line.second
    new_lines.append(DeductiveProof.Line(first_mp_conclusion, 0, [part_1_mp_index, len(new_lines) - 1]))
    second_MP_conclusion = first_mp_conclusion.second
    new_lines.append(DeductiveProof.Line(second_MP_conclusion, 0, [part_2_mp_index, len(new_lines) - 1]))
    return DeductiveProof(new_statement, proof_true.rules, new_lines)


def proof_or_counterexample_implies_not(formula):
    """ Return either a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT, or a
        model where formula does not hold. It is assumed that formula may only
        have the operators implies and not in it """
    # Task 6.3


def prove_in_model(formula, model):
    def prove_in_model_helper(formula: formula, model: dict):

        if is_constant(formula.root):
            if formula.root == 'T':
                lines.append(
                    DeductiveProof.Line(formula, AXIOMATIC_DICT['T'], []))  # add T, derived for free from T rule
            else:  # it is F
                # TODO ain't so simple
                lines.append(
                    DeductiveProof.Line(formula, AXIOMATIC_DICT['NF'], []))  # add ~F derived for free from NF rule

        if is_variable(formula.root):
            return formula

        elif only_implies_not(formula):
            return prove_in_model_implies_not(formula, model)

        elif is_unary(formula.root):
            # TODO okay, here we assume that both & and | will take care of ~ themselves , meaning will return the right fomrula
            return prove_in_model_helper(formula.first, model)

        elif formula.root == '&':
            # A = InferenceRule([], Formula.from_infix('(p->(q->(p&q)))'))
            if evaluate(formula, model):  # (p->(q->(p&q)))
                pass
                # NA1 = InferenceRule([], Formula.from_infix('(~p->~(p&q))'))
                # NA2 = InferenceRule([], Formula.from_infix('(~q->~(p&q))'))

        # (p|q)
        elif formula.root == '|':
            # index = None  # either p or q index to reference in justification
            if evaluate(formula.first, model):  # p is true
                p = prove_in_model_helper(formula.first, model)  # we assume p is within our lines
                p_index = find_index_by_conclusion(p, lines)
                lines.append(DeductiveProof.Line(Formula('->', p, formula), AXIOMATIC_DICT['O1'], None))  # p->(p|q)
                lines.append(DeductiveProof.Line(formula, 0, [p_index, len(lines) - 1]))  # we just proved formula
                return formula

            elif evaluate(formula.second, model):  # q is true
                q = prove_in_model_helper(formula.second, model)  # we assume q is within our lines
                q_index = find_index_by_conclusion(q, lines)
                lines.append(DeductiveProof.Line(Formula('->', q, formula), AXIOMATIC_DICT['O2'], None))  # p->(p|q)
                lines.append(DeductiveProof.Line(formula, 0, [q_index, len(lines) - 1]))  # we just proved formula
                return formula

            else:  # q and p are false
                # NO = InferenceRule([], Formula.from_infix('(~p->(~q->~(p|q)))'))
                # TODO we can derive from double MP ~(p|q) but how can we get (p|q) from that ????
                not_p = prove_in_model_helper(Formula('~', formula.first), model)
                not_q = prove_in_model_helper(Formula('~', formula.second), model)
                not_p_index = find_index_by_conclusion(not_p, lines)  # ~p
                not_q_index = find_index_by_conclusion(not_q, lines)  # ~q
                core = Formula('~', formula)  # ~(p|q)
                part_2 = Formula(not_q, core)  # (~q->~(p|q)
                no = Formula('->', not_p, part_2)  # (~p->(~q->~(p|q)))
                lines.append(DeductiveProof.Line(no, AXIOMATIC_DICT['NO'], None))  # here we entered (~p->(~q->~(p|q)))
                lines.append(DeductiveProof.Line(part_2, 0, [not_q_index, len(lines) - 1]))  # entered (~q->~(p|q))
                lines.append(DeductiveProof.Line(formula, 0, [not_p_index, len(lines) - 1]))  # entered ~(p|q)
                return core

                # TODO 2.0 i Think i get it! if we entered here, it means that (p|q) is actually false in this model, meaning we got called from ~(p|q)

    def only_implies_not(formula):
        """
        :param formula: The formula to be checked
        :return: if formula only contains the signs implies , not.
        """
        prefix = formula.prefix()
        prefix = prefix.replace('->', 'א')
        for char in prefix:
            if char != 'א' and not is_unary(char):  # char is not -> or ~:
                if not is_variable(char):  # char is one of |&TF
                    return False
        return True

    """ Return a proof of formula via AXIOMATIC_SYSTEM from the assumptions
        that all variables are valued as in model, with the assumptions being
        ordered alphabetically by the names of the variables. It is assumed
        that formula is true in model """
    variables = sorted(list(formula.variables()))
    assumptions = []
    for var in variables:
        if model[var] is True:
            assumptions.append(Formula(var))
        else:
            assumptions.append(Formula('~', Formula(var)))

    statement = InferenceRule(assumptions, formula)
    lines = [DeductiveProof.Line(ass, None, None) for ass in assumptions]
    prove_in_model_helper(formula, model)
    return DeductiveProof(statement, AXIOMATIC_SYSTEM, lines)

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


    # prove_in_model(Formula.from_infix('(p|q)'), {'p':True})
