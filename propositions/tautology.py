""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/tautology.py """

from propositions.syntax import *
from propositions.proofs import *
from propositions.provers import MP, I1, I2, inverse_mp
from propositions.semantics import *
import math

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
                  'NO': 11, 'T': 12, 'NF': 13, 'R': 14}


def find_index_by_conclusion(conclusion, lines):
    for index, line in enumerate(lines):
        if line.conclusion == conclusion:
            return index
    return None


def find_index(p, p_index, q, q_index, lines):
    for line_index, line in enumerate(lines):
        if line.conclusion == p:
            p_index = line_index
        elif line.conclusion == q:
            q_index = line_index
    return p_index, q_index


def prove_in_model_implies_not_helper(formula, model: dict, lines: list):
    # just var
    if is_variable(formula.root):
        return formula

    # (psi -> psi)
    elif is_binary(formula.root):  # root is ->
        return prove_for_is_implication_for_implies_not(formula, model, lines)

    # elif is_unary(formula.root) and not is_variable(formula.first.root): #
    elif is_unary(formula.root):
        return prove_for_is_unary_implies_not(formula, model, lines)


def prove_for_is_unary_implies_not(formula, model, lines):
    if is_unary(formula.first.root):  # the next root is ~
        p = prove_in_model_implies_not_helper(formula.first.first, model, lines)
        line_1_to_add = Formula(NEGATE_OPERATOR, Formula(NEGATE_OPERATOR, p))
        p_index = find_index_by_conclusion(p, lines)
        NN_line = Formula(IMPLICATION_OPERATOR, p, line_1_to_add)
        lines.append(DeductiveProof.Line(NN_line, 5, []))
        MP_line = NN_line.second
        lines.append(DeductiveProof.Line(MP_line, 0, [p_index, len(lines) - 1]))
        return MP_line

    elif is_variable(formula.first.root):
        return Formula('~', prove_in_model_implies_not_helper(formula.first, model, lines))

    else:  # we have ~ and psi, deal with NI
        p = prove_in_model_implies_not_helper(formula.first.first, model, lines)  # ps1_1
        not_q = prove_in_model_implies_not_helper(Formula('~', formula.first.second), model, lines)  # not_psi_2
        part_2 = Formula(IMPLICATION_OPERATOR, not_q, formula)  # (~psi2 -> ~(psi_1 -> psi_2))
        ni = Formula(IMPLICATION_OPERATOR, p, part_2)  # (psi_1 -> (~psi2 -> ~(psi_1 -> psi_2)))
        lines.append(DeductiveProof.Line(ni, 4, []))
        # I run on all the lines and search for 'p' to proof the line with MP
        # I know that p and ~q must appear as an assumption in the lines of the proof
        p_index = -1
        p_index = find_index_by_conclusion(p, lines)
        q_index = -2
        q_index = find_index_by_conclusion(not_q, lines)

        # p_index, q_index = find_index(p, p_index, not_q, q_index, lines)
        # if p_index == -1 or q_index == -2:
        #     print("bad index, p is: {}, q is: {}".format(p, not_q))
        #     exit(-1)
        # add line 2 as an MP conclusion for
        lines.append(DeductiveProof.Line(part_2, 0, [p_index, len(lines) - 1]))
        lines.append(DeductiveProof.Line(formula, 0, [q_index, len(lines) - 1]))
        return formula


def prove_for_is_implication_for_implies_not(formula, model, lines):
    if evaluate(formula.first, model) is False:  # psi_1 is not true in M
        not_p = prove_in_model_implies_not_helper(Formula('~', formula.first), model, lines)
        l3 = Formula(IMPLICATION_OPERATOR, not_p, formula)
        lines.append(DeductiveProof.Line(l3, 3, []))  # from I3
        # l2 = Formula(IMPLICATION_OPERATOR, p, q)  # build psi_1->psi_2
        not_p_index = find_index_by_conclusion(not_p, lines)
        if not_p_index is None:
            print('we got a not found conclusion:', not_p_index, 'for conclusion:', not_p)
            exit(-1)
        lines.append(DeductiveProof.Line(formula, 0, [not_p_index, len(lines) - 1]))  # from I2
        return formula

    elif evaluate(formula.second, model) is True:  # psi_2 is True in M
        p = prove_in_model_implies_not_helper(formula.first, model, lines)
        q = prove_in_model_implies_not_helper(formula.second, model, lines)
        l1 = Formula(IMPLICATION_OPERATOR, q, Formula(IMPLICATION_OPERATOR, p, q))  # build I1
        lines.append(DeductiveProof.Line(l1, 1, []))  # from I1
        l2 = Formula(IMPLICATION_OPERATOR, p, q)  # build psi_1->psi_2
        find_q_index = find_index_by_conclusion(q, lines)
        lines.append(DeductiveProof.Line(l2, 0, [find_q_index, len(lines) - 1]))  # from I2
        return l2

    else:
        print('OOOMMMMGGGGGGGG , wrong input or somthing went wrong with recurtion')
        exit(-1)
        return


def prove_in_model_implies_not(formula, model):
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
    prove_in_model_implies_not_helper(formula, model, lines)
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

    new_lines = []  # init the list of new lines for the proof

    last_true_assumption, new_lines, new_statement, part_1_mp_index, part_2_mp_index = create_inverse_mp_proofs(
        new_lines, proof_false,
        proof_true)

    # first MP to isolate ((~q->p)->p) from R
    p = proof_true.statement.conclusion
    q = last_true_assumption
    R_line = Formula(IMPLICATION_OPERATOR, Formula(IMPLICATION_OPERATOR, q, p), Formula(IMPLICATION_OPERATOR,
                                                                                        Formula(IMPLICATION_OPERATOR,
                                                                                                Formula(NEGATE_OPERATOR,
                                                                                                        q), p), p))
    # need to search for the rule number for R ...
    rule_index_R = -3
    for rule_index, rule in enumerate(proof_true.rules):
        if rule == R:
            rule_index_R = rule_index
            break

    new_lines.append(DeductiveProof.Line(R_line, rule_index_R, []))  # added R line

    first_mp_conclusion = R_line.second
    # added first MP conclusion
    new_lines.append(DeductiveProof.Line(first_mp_conclusion, 0, [part_1_mp_index, len(new_lines) - 1]))
    second_MP_conclusion = first_mp_conclusion.second

    # added second MP conclusion
    new_lines.append(DeductiveProof.Line(second_MP_conclusion, 0, [part_2_mp_index, len(new_lines) - 1]))
    return DeductiveProof(new_statement, proof_true.rules, new_lines)


def create_inverse_mp_proofs(new_lines, proof_false, proof_true):
    """
    help method for reduce_assumption function. it calculates the inverse_mp of the two proofs, and add their lines
    to the new_lines list
    :param new_lines:
    :param proof_false:
    :param proof_true:
    :return:
    """
    ######### do inverse_mp to the true proof ############
    last_true_assumption = proof_true.statement.assumptions[len(proof_true.statement.assumptions) - 1]
    inverse_proof_true = inverse_mp(proof_true, last_true_assumption)
    ######### finished inverse_mp ############
    ######### initiated statement for the new proof ############
    new_assumption = inverse_proof_true.statement.assumptions
    new_conclusion = proof_true.statement.conclusion
    new_statement = InferenceRule(new_assumption, new_conclusion)
    ######### finish init statement ############
    new_lines += inverse_proof_true.lines  # added lines of the first true proof
    part_1_mp_index = len(new_lines) - 1  # get the line index for the true proof's conclusion
    ######### do inverse_mp to the false proof ############
    last_false_assumption = proof_false.statement.assumptions[len(proof_false.statement.assumptions) - 1]
    inverse_proof_false = inverse_mp(proof_false, last_false_assumption)
    ######### finished inverse_mp ############
    ######### adding line of the false proof, while changing the line numbers according to the new proof ############
    current_new_line_index = len(new_lines)
    for line_index, line in enumerate(inverse_proof_false.lines):
        new_justification = None
        if line.justification is not None:
            new_justification = [a + current_new_line_index for a in line.justification]

        new_lines.append(DeductiveProof.Line(line.conclusion, line.rule, new_justification))
    ######### finish adding line of false proof ############

    part_2_mp_index = len(new_lines) - 1  # get the line index for the false proof's conclusion
    return last_true_assumption, new_lines, new_statement, part_1_mp_index, part_2_mp_index


def proof_or_counterexample_implies_not(formula):
    """ Return either a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT, or a
        model where formula does not hold. It is assumed that formula may only
        have the operators implies and not in it """
    # Task 6.3
    proof_list = []
    # create list of proofs by model
    all_models_list = list(all_models(sorted(list(formula.variables()))))
    for model in all_models_list:

        if not evaluate(formula, model):
            return model
        else:
            proof_list.append(prove_in_model_implies_not(formula, model))
    # run on each level of the tree
    tree_level_size = int(math.log(len(proof_list), 2))
    temp_proof_list = []
    for tree_level in range(0, tree_level_size):
        # run on each
        for proof_index in range(0, len(proof_list), 2):
            temp_proof_list.append(reduce_assumption(proof_list[proof_index + 1], proof_list[proof_index]))

        proof_list = temp_proof_list
        temp_proof_list = []
    assert len(proof_list) == 1
    return proof_list[0]
    # Task 6.3


def prove_in_model(formula, model):
    def prove_in_model_helper(formula: formula, model: dict):
        if is_variable(formula.root):
            return formula

        elif only_implies_not(formula):
            return prove_in_model_implies_not_helper(formula, model, lines)

        elif is_unary(formula.root):
            return prove_for_is_unary(formula, model, lines)

        elif formula.root == '&':
            # (p->(q->(p&q)))
            if evaluate(formula, model):  # (p->(q->(p&q))) - both p and q are correct
                return prove_and_True_True(formula, model)
        # (p|q)
        elif formula.root == '|':
            if evaluate(formula.first, model):  # p is true
                return prove_or_p_is_true(formula, model)

            elif evaluate(formula.second, model):  # q is true
                return prove_or_q_is_true(formula, model)

        elif formula.root == IMPLICATION_OPERATOR:
            return prove_for_is_implication(formula, model, lines)

        elif is_constant(formula.root) and formula.root == 'T':
            lines.append(DeductiveProof.Line(formula, AXIOMATIC_DICT['T'], []))  # add T, derived for free from T rule
            return formula

    def prove_for_is_unary(formula, model, lines):
        if is_unary(formula.first.root):  # the next root is ~
            p = prove_in_model_helper(formula.first.first, model)
            line_1_to_add = Formula(NEGATE_OPERATOR, Formula(NEGATE_OPERATOR, p))
            p_index = find_index_by_conclusion(p, lines)
            NN_line = Formula(IMPLICATION_OPERATOR, p, line_1_to_add)
            lines.append(DeductiveProof.Line(NN_line, 5, []))
            MP_line = NN_line.second
            lines.append(DeductiveProof.Line(MP_line, 0, [p_index, len(lines) - 1]))
            return MP_line

        elif is_variable(formula.first.root):
            return Formula('~', prove_in_model_helper(formula.first, model))

        elif formula.first.root == 'F':
            lines.append(DeductiveProof.Line(formula, AXIOMATIC_DICT['NF'], []))  # add ~F derived for free from NF rule
            return Formula('~', Formula('F'))

        elif formula.first.root == '&':
            # check if p is false and use ~p->~(p&q))
            if evaluate(formula.first.second, model) or not evaluate(formula.first.first, model):
                # q is true, p is false (because overall formula and model is false)
                # if both false , just pick ~p
                return prove_and_false_true_and_false_false(formula.first, model)

                # check if q is false and use (~q->~(p&q))
            elif evaluate(formula.first.first,
                          model):  # p is true, q is false (because overall formula and model is false)
                return prove_and_true_false(formula.first, model)

        elif formula.first.root == '|':
            return prove_or_notp_notq(formula.first, model)

        else:  # we have ~ and psi, deal with NI
            p = prove_in_model_helper(formula.first.first, model)  # ps1_1
            not_q = prove_in_model_helper(Formula('~', formula.first.second), model)  # not_psi_2
            part_2 = Formula(IMPLICATION_OPERATOR, not_q, formula)  # (~psi2 -> ~(psi_1 -> psi_2))
            ni = Formula(IMPLICATION_OPERATOR, p, part_2)  # (psi_1 -> (~psi2 -> ~(psi_1 -> psi_2)))
            lines.append(DeductiveProof.Line(ni, 4, []))
            # I run on all the lines and search for 'p' to proof the line with MP
            # I know that p and ~q must appear as an assumption in the lines of the proof
            p_index = -1
            q_index = -2
            p_index, q_index = find_index(p, p_index, not_q, q_index, lines)
            # add line 2 as an MP conclusion for
            lines.append(DeductiveProof.Line(part_2, 0, [p_index, len(lines) - 1]))
            lines.append(DeductiveProof.Line(formula, 0, [q_index, len(lines) - 1]))
            return formula

    def prove_for_is_implication(formula, model, lines):
        if evaluate(formula.first, model) is False:  # psi_1 is not true in M
            not_p = prove_in_model_helper(Formula('~', formula.first), model)
            l3 = Formula(IMPLICATION_OPERATOR, not_p, formula)
            lines.append(DeductiveProof.Line(l3, 3, []))  # from I3
            # l2 = Formula(IMPLICATION_OPERATOR, p, q)  # build psi_1->psi_2
            not_p_index = find_index_by_conclusion(not_p, lines)
            if not_p_index is None:
                print('we got a not found conclusion:', not_p_index, 'for conclusion:', not_p)
                exit(-1)
            lines.append(DeductiveProof.Line(formula, 0, [not_p_index, len(lines) - 1]))  # from I2
            return formula
        # test a

        elif evaluate(formula.second, model) is True:  # psi_2 is True in M
            p = prove_in_model_helper(formula.first, model)
            q = prove_in_model_helper(formula.second, model)
            l1 = Formula(IMPLICATION_OPERATOR, q, Formula(IMPLICATION_OPERATOR, p, q))  # build I1
            lines.append(DeductiveProof.Line(l1, 1, []))  # from I1
            l2 = Formula(IMPLICATION_OPERATOR, p, q)  # build psi_1->psi_2
            find_q_index = find_index_by_conclusion(q, lines)
            lines.append(DeductiveProof.Line(l2, 0, [find_q_index, len(lines) - 1]))  # from I2
            return l2

    def prove_or_notp_notq(formula, model):
        """
        :param formula: cur formula to work on
        :param model: model to check if formula is true or false
        :return: appends appropriate Lines to lines and returns ~(p|q)
        """
        not_p = prove_in_model_helper(Formula('~', formula.first), model)
        not_q = prove_in_model_helper(Formula('~', formula.second), model)
        not_p_index = find_index_by_conclusion(not_p, lines)  # ~p
        not_q_index = find_index_by_conclusion(not_q, lines)  # ~q
        core = Formula('~', formula)  # ~(p|q)
        part_2 = Formula(IMPLICATION_OPERATOR, not_q, core)  # (~q->~(p|q)
        no = Formula(IMPLICATION_OPERATOR, not_p, part_2)  # (~p->(~q->~(p|q)))
        lines.append(DeductiveProof.Line(no, AXIOMATIC_DICT['NO'], []))  # here we entered (~p->(~q->~(p|q)))
        lines.append(DeductiveProof.Line(part_2, 0, [not_p_index, len(lines) - 1]))  # entered (~q->~(p|q))
        lines.append(DeductiveProof.Line(core, 0, [not_q_index, len(lines) - 1]))  # entered ~(p|q)
        return core

    def prove_or_q_is_true(formula, model):
        """
        :param formula: cur formula to work on
        :param model: model to check if formula is true or false, we know q is true
        :return: appends appropriate Lines to lines and returns (p|q)
        """
        q = prove_in_model_helper(formula.second, model)  # we assume q is within our lines
        q_index = find_index_by_conclusion(q, lines)
        lines.append(DeductiveProof.Line(Formula(IMPLICATION_OPERATOR, q, formula), AXIOMATIC_DICT['O2'], []))  # p->(p|q)
        lines.append(DeductiveProof.Line(formula, 0, [q_index, len(lines) - 1]))  # we just proved formula
        return formula

    def prove_or_p_is_true(formula, model):
        """
        :param formula: cur formula to work on
        :param model: model to check if formula is true or false, we know p is true
        :return: appends appropriate Lines to lines and returns (p|q)
        """
        p = prove_in_model_helper(formula.first, model)  # we assume p is within our lines
        p_index = find_index_by_conclusion(p, lines)
        lines.append(DeductiveProof.Line(Formula(IMPLICATION_OPERATOR, p, formula), AXIOMATIC_DICT['O1'], []))  # p->(p|q)
        lines.append(DeductiveProof.Line(formula, 0, [p_index, len(lines) - 1]))  # we just proved formula
        return formula

    def prove_and_true_false(formula, model):
        """
        we know q is false, using NA2 we derive ~(p&q)
        :param formula: cur formula to work on
        :param model: model to check if formula is true or false
        :return: appends appropriate Lines to lines and returns ~(p|q)
        """
        not_q = prove_in_model_helper(Formula('~', formula.second), model)  # ~q
        not_q_index = find_index_by_conclusion(not_q, lines)
        no = Formula(IMPLICATION_OPERATOR, not_q, Formula('~', formula))  # (~q->~(p&q))
        lines.append(DeductiveProof.Line(no, AXIOMATIC_DICT['NA2'], []))  # here we entered (~p->(~(p&q)))
        lines.append(DeductiveProof.Line(Formula('~', formula), 0, [not_q_index, len(lines) - 1]))  # entered ~(p&q)
        return Formula('~', formula)

    def prove_and_false_true_and_false_false(formula, model):
        """
        we know q is false, using NA2 we derive ~(p&q)
        :param formula: cur formula to work on
        :param model: model to check if formula is true or false
        :return: appends appropriate Lines to lines and returns ~(p|q)
        """
        not_p = prove_in_model_helper(Formula('~', formula.first), model)  # ~p
        not_p_index = find_index_by_conclusion(not_p, lines)
        no = Formula(IMPLICATION_OPERATOR, not_p, Formula('~', formula))  # (~p->~(p&q))
        lines.append(DeductiveProof.Line(no, AXIOMATIC_DICT['NA1'], []))  # here we entered (~p->(~(p|q)))
        lines.append(DeductiveProof.Line(Formula('~', formula), 0, [not_p_index, len(lines) - 1]))  # entered (p|q)
        return Formula('~', formula)

    def prove_and_True_True(formula, model):
        """
        we know p and q are true  A we derive (p&q)
        :param formula: cur formula to work on
        :param model: model to check if formula is true or false
        :return: appends appropriate Lines to lines and returns (p|q)
        """
        p = prove_in_model_helper(formula.first, model)  # p
        q = prove_in_model_helper(formula.second, model)  # q
        p_index = find_index_by_conclusion(p, lines)
        q_index = find_index_by_conclusion(q, lines)
        part_2 = Formula(IMPLICATION_OPERATOR, q, formula)  # (q->(p&q)
        no = Formula(IMPLICATION_OPERATOR, p, part_2)  # (p->(q->(p&q)))
        lines.append(DeductiveProof.Line(no, AXIOMATIC_DICT['A'], []))  # here we entered (p->(q->(p&q)))
        lines.append(DeductiveProof.Line(part_2, 0, [p_index, len(lines) - 1]))  # entered (q->(p&q))
        lines.append(DeductiveProof.Line(formula, 0, [q_index, len(lines) - 1]))  # entered (p&q)
        return formula

    def only_implies_not(formula):
        """
        :param formula: The formula to be checked
        :return: if formula only contains the signs implies , not.
        """
        prefix = formula.prefix()
        prefix = prefix.replace(IMPLICATION_OPERATOR, 'א')
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
    proof_list = []
    # create list of proofs by model
    all_models_list = list(all_models(sorted(list(formula.variables()))))
    for model in all_models_list:

        if not evaluate(formula, model):
            return model
        else:
            proof_list.append(prove_in_model(formula, model))
    # run on each level of the tree
    tree_level_size = int(math.log(len(proof_list), 2))
    temp_proof_list = []
    for tree_level in range(0, tree_level_size):
        # run on each
        for proof_index in range(0, len(proof_list), 2):
            temp_proof_list.append(reduce_assumption(proof_list[proof_index + 1], proof_list[proof_index]))

        proof_list = temp_proof_list
        temp_proof_list = []
    assert len(proof_list) == 1

    return proof_list[0]
    # Task 6.5


def proof_or_counterexample_for_inference(rule):
    """ Return either a proof of rule via AXIOMATIC_SYSTEM, or a model where
        rule does not hold """

    if rule.assumptions == []:
        return proof_or_counterexample(rule.conclusion)
    else:
        lines = []
        for ass in rule.assumptions:
            lines.append(DeductiveProof.Line(ass, None, []))
        formula = rule.conclusion
        for index in range((len(rule.assumptions) - 1), -1, -1):
            formula = Formula(IMPLICATION_OPERATOR, rule.assumptions[index], formula)
        cur_proof_or_counter = proof_or_counterexample(formula)
        if type(cur_proof_or_counter) == dict:
            return cur_proof_or_counter  # this is a modle with a counter example for rule
        else:  # we have a proof
            cur_line_counter = len(lines)
            for line in cur_proof_or_counter.lines:
                justifications = []
                for just in line.justification:
                    justifications.append(just + cur_line_counter)
                lines.append(DeductiveProof.Line(line.conclusion, line.rule, justifications))
            for run in range(len(rule.assumptions)):
                formula = formula.second
                lines.append(DeductiveProof.Line(formula, 0, [run, len(lines) - 1]))
        returned_proof = DeductiveProof(rule, AXIOMATIC_SYSTEM, lines)
        return returned_proof


def model_or_inconsistent(formulae):
    """ Return either a model where all of formulae hold, or a list of two
        proofs, both from formulae via AXIOMATIC_SYSTEM, the first of some
        formula and the second of the negation of the same formula """
    variable_set = set
    for formula in formulae:
        variable_set = variable_set.union((formula.variables()))
    # check if there exists a model on which all formulas in formulae are True
    all_models_list = list(all_models(sorted(list(variable_set))))
    for model in all_models_list:
        eval_result_list = []
        for formula in formulae:
            if evaluate(formula, model):
                eval_result_list.append(True)
            else:
                eval_result_list.append(False)
        if False not in eval_result_list:
            return model

    proof_1_formula = create_new_formula(formulae)
    proof_2_formula = Formula(NEGATE_OPERATOR, proof_1_formula)

    # proof_1_assumptions = [InferenceRule([],formula) for formula in formulae]
    proof_1_statement = InferenceRule(formulae, proof_1_formula)
    #### INSERT HERE TASK 6 SOLUTION FOR PROOF 1 ############
    proof_1 = proof_or_counterexample_for_inference(proof_1_statement)
    assert proof_1.is_valid()

    #### FINISHED TASK 6 IMPLEMENTATION ############

    # proof 2 is a tautology. then prove it!
    proof_2_statement = InferenceRule(formulae, proof_2_formula)
    proof_2 = proof_or_counterexample_for_inference(proof_2_statement)

    return [proof_1, proof_2]


def create_new_formula(formulae):
    """
    help method for model_or_inconsistent, to create an 'and' formula with all the original formulas together
    :param formulae:
    :return:
    """
    if len(formulae) == 1:
        return formulae[0]
    return Formula(AND_OPERATOR, formulae[0], create_new_formula(formulae[1:]))


