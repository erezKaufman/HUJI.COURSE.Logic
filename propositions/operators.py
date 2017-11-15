""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/operators.py """

from propositions.syntax import *
from propositions.semantics import *

F = Formula


def change_root(s):
    """

    :param s:
    :return:
    """
    root = None
    first = None
    second = None
    if s[0] == '&' or s[0] == '|':
        root = s[0]
        first = create_to_not_and_or(s[1:])
        s = F.string
        second = create_to_not_and_or(s)
        # Formula.string = s
    elif s[0] == '-':
        if s[1] == '>':  # if that was an implication operator
            root = OR_OPERATOR
            first = Formula(NEGATE_OPERATOR, create_to_not_and_or(s[2:]))
            s = F.string
            second = create_to_not_and_or(s)
        else:
            root = NEGATE_OPERATOR
            temp_root = s[1]
            temp_first = create_to_not_and_or(s[2:])
            s = F.string
            temp_second = create_to_not_and_or(s)
            first = F(temp_root, temp_first, temp_second)

    elif s[0] == '<':
        root = OR_OPERATOR
        temp_first = create_to_not_and_or(s[3:])
        s = F.string
        temp_second = create_to_not_and_or(s)
        first = F(AND_OPERATOR, temp_first, temp_second)
        second = F(AND_OPERATOR, F(NEGATE_OPERATOR, temp_first), F(NEGATE_OPERATOR, temp_second))

    return root, first, second


def create_to_not_and_or(s):
    F.string = s
    if is_unary(s[0]):
        F.string = s[1:]
        return F(s[0], create_to_not_and_or(s[1:]))
    elif is_variable(s[0]) or is_constant(s[0]):
        #  if the first letter is a variable, we want to check if the next to letters are digits
        return_var = ''
        if len(s) > 1 and s[1].isdigit():
            if len(s) > 2 and s[2].isdigit():
                F.string = s[3:]
                return_var = s[0:3]
            else:
                F.string = s[2:]
                return_var = s[0:2]
        else:
            if len(s) > 1:
                F.string = s[1:]
            return_var = s[0]
        return F(return_var)
    elif is_binary(s[0]):
        root, first, second = change_root(s)
        return F(root, first, second)
    else:  # else it's the MUX!

        root = OR_OPERATOR
        temp_first = create_to_not_and_or(s[2:])
        s = F.string
        temp_second = create_to_not_and_or(s)
        s = F.string
        temp_third = create_to_not_and_or(s)
        first = F(AND_OPERATOR, temp_third, F(OR_OPERATOR, temp_second, F(NEGATE_OPERATOR, temp_first)))
        second = F(AND_OPERATOR, temp_first, temp_second)
        return F(root, first, second)


def to_not_and_or(formula):
    """ Return an equivalent formula that has no operators beyond not, and, and
        or """
    return create_to_not_and_or(formula.prefix())



def to_not_and_helper(form,false_sign,true_sign):
    """ the help functino will replace every use of OE (= p|q)with combinations of NOT and AND (= ~(~p&~q) )
        also, when encountered with a constant, we will replace it with our own truth sign"""
    if is_variable(form.root):
        return form
    elif is_constant(form.root):
        return true_sign if form.root == TRUE_IN_FORM else false_sign
    elif form.root == OR_OPERATOR:
        first = to_not_and_helper(form.first,false_sign,true_sign)
        second = to_not_and_helper(form.second,false_sign,true_sign)
        return F(NEGATE_OPERATOR, F(AND_OPERATOR, F(NEGATE_OPERATOR, first), F(NEGATE_OPERATOR, second)))
    else:
        form.first = to_not_and_helper(form.first,false_sign,true_sign)
        if not is_unary(form.root):
            form.second = to_not_and_helper(form.second,false_sign,true_sign)
        return form


def to_not_and(formula):
    """ Return an equivalent formula that has no operators beyond not and and,
        and has no constants """
    init_formula = to_not_and_or(formula)
    variable = list(init_formula.variables()) #return the variables list of the formula
    if len(variable) == 0:
        return None  #just in case we didn't have any variables.
    false_sign = F(AND_OPERATOR,F(variable[0]),F(NEGATE_OPERATOR,F(variable[0]))) # create your own beautiful false sign
    true_sign = F(NEGATE_OPERATOR,false_sign) # create a true sign
    return to_not_and_helper(init_formula,false_sign,true_sign)


def synthesize_not_and(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond not
        and and, and has no constants """
    formula = synthesize(models,values)
    return to_not_and(formula)


def to_implies_false_helper(formula):
    if is_variable(formula.root):
        return formula
    elif formula.root == AND_OPERATOR:
        first = to_implies_false_helper(formula.first)
        second = to_implies_false_helper(formula.second)
        negate_second = F(IMPLICATION_OPERATOR,second,F(FALSE_IN_FORM))
        negate_first_second = F(IMPLICATION_OPERATOR,F(IMPLICATION_OPERATOR,first,negate_second),F(FALSE_IN_FORM))
        return negate_first_second
    elif is_unary(formula.root):
        first = to_implies_false_helper(formula.first)
        return F(IMPLICATION_OPERATOR,first,F(FALSE_IN_FORM))
    else:
        formula.first = to_implies_false_helper(formula.first)
        formula.second = to_implies_false_helper(formula.second)
        return formula

def to_implies_false(formula):
    """ Return an equivalent formula that has no operators beyond implies, and
        has no constants beyond false """
    temp_formulat = to_not_and(formula)
    return to_implies_false_helper(temp_formulat)



def synthesize_implies_false(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond
        implies, and has no constants beyond false """
    temp_formula = synthesize_not_and(models,values)
    return to_implies_false(temp_formula)

# (p-&(p-&p)) = NOT P
#
def to_nand_helper(formula, true_from_nand):
    if is_variable(formula.root):
        return formula
    elif formula.root == AND_OPERATOR:
        first = to_nand_helper(formula.first, true_from_nand)
        second = to_nand_helper(formula.second, true_from_nand)
        nand_first_second = F(NAND_OPERATOR,first,second)
        return F(NAND_OPERATOR,nand_first_second,true_from_nand)
    elif is_unary(formula.root):
        first = to_nand_helper(formula.first, true_from_nand)
        return F(NAND_OPERATOR,first,true_from_nand)
    else:
        formula.first = to_nand_helper(formula.first, true_from_nand)
        formula.second = to_nand_helper(formula.second, true_from_nand)
        return formula


def to_nand(formula):
    """ Return an equivalent formula that has no operators beyond nand, and has
        no constants """
    temp_formula = to_not_and(formula)
    variable_formula = F(list(temp_formula.variables())[0])
    true_from_nand = F(NAND_OPERATOR,variable_formula,F(NAND_OPERATOR,variable_formula,variable_formula))
    return to_nand_helper(temp_formula,true_from_nand)





def synthesize_nand(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond nand,
        and has no constants """
    temp_formula = synthesize_not_and(models,values)
    return to_nand(temp_formula)


def to_nor_helper(formula,synthesized_false):
    if is_variable(formula.root):
        return formula
    elif formula.root == AND_OPERATOR:
        first = to_nor_helper(formula.first, synthesized_false)
        second = to_nor_helper(formula.second, synthesized_false)
        nor_first = F(NOR_OPERATOR,first,synthesized_false)
        nor_second = F(NOR_OPERATOR,second,synthesized_false)
        return F(NOR_OPERATOR,nor_first,nor_second)
    elif is_unary(formula.root):
        first = to_nor_helper(formula.first, synthesized_false)
        return F(NOR_OPERATOR,first,synthesized_false)
    else:
        formula.first = to_nor_helper(formula.first, synthesized_false)
        formula.second = to_nor_helper(formula.second, synthesized_false)
        return formula


def to_nor(formula):
    """ Return an equivalent formula that has no operators beyond nor, and has
        no constants """
    temp_formula = to_not_and(formula)
    variable_formula = F(list(temp_formula.variables())[0])

    temp_synthesized_false = F(NOR_OPERATOR,variable_formula,variable_formula)
    synthesized_false = F(NOR_OPERATOR,variable_formula,temp_synthesized_false)
    return to_nor_helper(temp_formula,synthesized_false)



def synthesize_nor(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond nor,
        and has no constants """
    temp_formula = synthesize_not_and(models,values)
    return to_nor(temp_formula)


def to_mux(formula):
    """ Return an equivalent formula that has no operators beyond mux """
    if is_variable(formula.root) or is_constant(formula.root):
        return formula
    elif is_unary(formula.root):
        first = to_mux(formula.first)
        return F(TERNARY_OPERATOR,first,F(FALSE_IN_FORM),F(TRUE_IN_FORM))
    elif formula.root == AND_OPERATOR:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        return F(TERNARY_OPERATOR,first,second,F(FALSE_IN_FORM))
    elif formula.root == OR_OPERATOR:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        return F(TERNARY_OPERATOR,first,F(TRUE_IN_FORM),second)
    elif formula.root == NAND_OPERATOR:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        first_second_and = F(TERNARY_OPERATOR,first,second,F(FALSE_IN_FORM))
        return F(TERNARY_OPERATOR,first_second_and,F(FALSE_IN_FORM),F(TRUE_IN_FORM))
    elif formula.root == NOR_OPERATOR:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        first_second_or = F(TERNARY_OPERATOR,first,F(TRUE_IN_FORM),second)
        return F(TERNARY_OPERATOR,first_second_or,F(FALSE_IN_FORM),F(TRUE_IN_FORM))
    elif formula.root == IMPLICATION_OPERATOR:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        return F(TERNARY_OPERATOR,first,second,F(TRUE_IN_FORM))
    elif formula.root == BICONDITIONAL_OPERATOR:
        # (p?q:(q?F:T))
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        second_mux = F(TERNARY_OPERATOR,second,F(FALSE_IN_FORM),F(TRUE_IN_FORM))
        return F(TERNARY_OPERATOR,first,second,second_mux)
    else:
        formula.first = to_mux(formula.first)
        formula.second = to_mux(formula.second)
        return formula
#     (p?(q?T:F):F)






def synthesize_mux(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond
        mux """
    temp_formula = synthesize(models,values)
    return to_mux(temp_formula)

