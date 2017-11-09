""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/operators.py """

from propositions.syntax import *
from propositions.semantics import *
F = Formula


def change_root(s):
    root = None
    first = None
    second = None
    if s[0] == '&' or s[0] == '|':
        root = s[0]
        first = create_to_not_and_or(s[1:])
        s = F.string
        second = create_to_not_and_or(s)
        Formula.string = s
    elif s[0] == '?':
        pass #TODO THINK
    elif s[0] == '-':
        if s[1] =='>': # if that was an implication operator
            root = OR_OPERATOR
            first = Formula(NEGATE_OPERATOR,create_to_not_and_or(s[2:]))
            s = F.string
            second = create_to_not_and_or(s)
        else:
            root = NEGATE_OPERATOR
            temp_root = s[1]
            temp_first = create_to_not_and_or(s[2:])
            s = F.string
            temp_second = create_to_not_and_or(s)
            first = F(temp_root,temp_first,temp_second)

    elif s[0] == '<':
        root = OR_OPERATOR
        temp_first =create_to_not_and_or(s[3:])
        s = F.string
        temp_second = create_to_not_and_or(s)
        first = F(AND_OPERATOR,temp_first,temp_second)
        second = F(AND_OPERATOR,F(NEGATE_OPERATOR,temp_first),F(NEGATE_OPERATOR,temp_second))

    return root , first, second

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
    else: # else it's the MUX!
        root = s[0:2] # ((p&T)&q)|((p&F)&r) => |&&Tpq&&Fpr
        first = create_to_not_and_or(s[2:])
        s = F.string
        second = create_to_not_and_or(s)
        s = F.string
        third = create_to_not_and_or(s)
        return F(root, first, second, third)



def to_not_and_or(formula):
    """ Return an equivalent formula that has no operators beyond not, and, and
        or """
    # return create_to_not_and_or(formula.prefix())
    string = formula.prefix()
    returning_string = ''
    for letter in range(len(string)):
        if string[letter] == '-':
            if string[letter+1] == '>':
                returning_string += OR_OPERATOR+NEGATE_OPERATOR
                letter+=1
            else:
                returning_string+= NEGATE_OPERATOR
        # elif string[letter] == '<':

    # if formula.root == NOR_OPERATOR:
    #
    #     pass
    # #    a-|b => ~a|b || -|ab => ~|ab
    # elif formula.root == NAND_OPERATOR:
    #     pass
    # #    a-&b => ~a&b || -&ab => ~&ab
    # elif  formula.root == IMPLICATION_OPERATOR:
    #     pass
    # #     ->ab => |~ab
    # elif formula.root == BICONDITIONAL_OPERATOR:
    #     pass
    # # <->ab => |&ab&~a~b
    # else:
#         (p?q:r) =>  ((r&(q|~p))|(p&q)) => |&&Tpq&&Fpr




def to_not_and(formula):
    """ Return an equivalent formula that has no operators beyond not and and,
        and has no constants """
    # Task 3.4.1

def synthesize_not_and(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond not
        and and, and has no constants """
    # Task 3.4.2

def to_implies_false(formula):
    """ Return an equivalent formula that has no operators beyond implies, and
        has no constants beyond false """
    # Task 3.5.1

def synthesize_implies_false(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond
        implies, and has no constants beyond false """
    # Task 3.5.2

def to_nand(formula):
    """ Return an equivalent formula that has no operators beyond nand, and has
        no constants """
    # Task 3.6.1

def synthesize_nand(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond nand,
        and has no constants """
    # Task 3.6.2

def to_nor(formula):
    """ Return an equivalent formula that has no operators beyond nor, and has
        no constants """
    # Task 3.7.1

def synthesize_nor(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond nor,
        and has no constants """
    # Task 3.7.2

def to_mux(formula):
    """ Return an equivalent formula that has no operators beyond mux """
    # Task 3.8.1

def synthesize_mux(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond
        mux """
    # Task 3.8.2
