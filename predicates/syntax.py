""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/syntax.py """

from propositions.syntax import Formula as PropositionalFormula
from predicates.util import *

def is_unary(s):
    """ Is s a unary operator? """
    return s == '~'

def is_binary(s):
    """ Is s a binary boolean operator? """
    return s == '&' or s == '|' or s == '->'

def is_equality(s):
    """ Is s the equality relation? """
    return s == "="

def is_quantifier(s):
    """ Is s a quantifier? """
    return s == "A" or s == "E"

def is_relation(s):
    """ Is s a relation name? """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()

def is_constant(s):
    """ Is s a constant name? """
    return  ((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd')) and s.isalnum()

def is_function(s):
    """ Is s a function name? """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()

def is_variable(s):
    """ Is s a variable name? """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()

def replace_string(s):
    """ this func is in charge of setting the rep string for Formula into opt's with length of 1,
    in order to stay within LL0 borders """
    ret = s
    ret = ret.replace('<->', 'ב')
    ret = ret.replace('->', 'א')
    ret = ret.replace('-&', 'ג')
    ret = ret.replace('-|', 'ד')
    ret = ret.replace('?:', 'ה')
    return ret

def switch_root_to_str(s):
    """ this func is called when creating a formula with a locally changed root """
    if s == 'א':
        return '->'
    elif s == 'ב':
        return '<->'
    elif s == 'ג':
        return '-&'
    elif s == 'ד':
        return '-|'
    elif s == 'ה':
        return '?'
    else:
        return s


def switch_root_to_ternary_prefix(s):  # special case for prefix
    """ special replace case for prefix"""
    if s == 'ה':
        return '?:'
    else:
        return s


def is_left_parenthese(s):
    return s == '('

def is_right_parenthese(s):
    return s == ')'


def is_comma(s):
    return s == ','


class Term:
    """ A term in a first order logical formula, composed from constant names
        and variable names, and function names applied to them """

    str = ''

    def __init__(self, root, arguments=None):
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            for x in arguments:
                assert type(x) is Term
            self.root = root
            self.arguments = arguments

    def __repr__(self):
        """ Return the usual (functional) representation of self """
        if is_constant(self.root) or is_variable(self.root):
            return (self.root)
        else:
            return_string = self.root + "("
            for arg in self.arguments:
                return_string += str(arg)
                if arg != self.arguments[-1]:
                    return_string += ","
            return_string += ")"
            return return_string

    def __eq__(self, other):
        return str(self) == str(other)
        
    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    @staticmethod
    def peek():
        if len(Term.str) == 1: return None
        return Term.str[1]

    @staticmethod
    def eat():
        if Term.peek():
            Term.str = Term.str[1:]
        else:
            Term.str = ''

    @staticmethod
    def parse_prefix(s):
        """ Parse a term from the prefix of a given string. Return a pair: the
            parsed term, and the unparsed remainder of the string """
        # s = replace_string(s)
        term_name = ''
        arguments = None
        Term.str = s
        while Term.str != '' and Term.str[0].isalnum():
            term_name += Term.str[0]
            Term.eat()
        if Term.str != '' and is_left_parenthese(Term.str[0]):
            arguments = []
            Term.eat()
            term_obj, Term.str = Term.parse_prefix(Term.str)
            arguments.append(term_obj)
            while is_comma(Term.str[0]):
                Term.eat()
                term_obj, Term.str = Term.parse_prefix(Term.str)
                arguments.append(term_obj)
            Term.eat()  # eat the right parentheses
        # elif is_comma(s[0]):
        #     while is_comma(s[0]):
        #         Term.eat()
        returned_term = Term(term_name, arguments)
        return returned_term, Term.str

    @staticmethod
    def parse(s):
        """ Return a term parsed from its given string representation """
        Term.str = s
        new_term = None
        while Term.str != '':
            new_term, Term.str = Term.parse_prefix(Term.str)
        return new_term




        # def variables_helper():
        #     cur = ''
        #     for index in range(len(Formula.str)):  # iterate on all char's of str
        #         if is_variable(Formula.str[index]):
        #             cur += Formula.str[index]  # we reached a var
        #             for dig in range(index + 1, len(Formula.str)):
        #                 if Formula.str[dig].isdigit():  # add all possible digits
        #                     cur += Formula.str[dig]
        #                     continue
        #                 index = dig - 1  # updates the index to last digits point
        #                 break
        #             self.formula_set.add(cur)  # adding the found var
        #             cur = ''  # resetting cur
        # """ Return the set of atomic propositions (variables) used in self """
        # self.formula_set = set() #holds the var set for the Formula
        # Term.str = self.prefix() # update Formula's str to be self's str rep
        # self.variables_helper() # updates formula's set
        # return self.formula_set

    def variables(self):
        def variables_helper(vars:set):
            if is_variable(self.root):
                vars.add(self.root)
            elif is_constant(self.root):
                return
            elif is_function(self.root):
                for arg in self.arguments:
                    vars.update(arg.variables())
            return
        """ Return the set of variables in this term """
        vars = set()  # holds the var set for the Formula
        variables_helper(vars) # updates formula's set
        return vars
        # Task 7.5

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this term """
        # Task 8.1.1

    def substitute_variables(self, substitution_map):
        """ Return a term obtained from this term where all the occurrences of
            each variable v that appears in the dictionary substitution_map are
            replaced with the term substitution_map[v] """
        for variable in substitution_map:
            assert is_variable(variable) and \
                   type(substitution_map[variable]) is Term
            # Task 9.1

    def substitute_constants(self, substitution_map):
        """ Return a term obtained from this formula where all the occurrences
            of each constant c that appears in the dictionary substitution_map
            are replaced with the term substitution_map[v] """
        for constant in substitution_map:
            assert is_constant(constant) and \
                   type(substitution_map[constant]) is Term
            # Ex12


class Formula:
    """ A Formula in first-order logic """

    def __init__(self, root, first=None, second=None):
        if is_relation(root):  # Populate self.root and self.arguments
            assert second is None
            for x in first:
                assert type(x) is Term
            self.root, self.arguments = root, first
        elif is_equality(root):  # Populate self.first and self.second
            assert type(first) is Term and type(second) is Term
            self.root, self.first, self.second = root, first, second
        elif is_quantifier(root): # Populate self.variable and self.predicate
            assert is_variable(first) and type(second) is Formula
            self.root, self.variable, self.predicate = root, first, second
        elif is_unary(root): # Populate self.first
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else: # Populate self.first and self.second
            assert is_binary(root) and type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second           

    def __repr__(self):
        """ Return the usual (infix for operators and equality, functional for
            other relations) representation of self """
        ret = ""
        if is_relation(self.root):
            ret += self.root + '('
            for obj in self.arguments:
                ret += str(obj)
                if obj != self.arguments[-1]:
                    ret += ','
            ret += ')'
        elif is_equality(self.root):
            ret = str(self.first) + self.root + str(self.second)
        elif is_quantifier(self.root):
            ret = self.root + str(self.variable) + '[' + str(self.predicate) + ']'
        elif is_unary(self.root):
            ret = self.root + str(self.first)
        elif is_binary(self.root):
            ret = '(' + str(self.first) + self.root + str(self.second) + ')'
        return ret
        # Task 7.2

    def __eq__(self, other):
        return str(self) == str(other)
        
    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    @staticmethod
    def parse_prefix(s):
        """ Parse a first-order formula from the prefix of a given string.
            Return a pair: the parsed formula, and unparsed remainder of the
            string """
        # Task 7.4.1

    @staticmethod
    def parse(s):
        """ Return a first-order formula parsed from its given string
            representation """
        # Task 7.4.2

    def free_variables(self):
        """ Return the set of variables that are free in this formula """
        # Task 7.6

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this formula """
        # Task 8.1.2

    def relations(self):
        """ Return a set of pairs (relation_name, arity) for all relation names
            that appear in this formula """
        # Task 8.1.3

    def substitute_variables(self, substitution_map):
        """ Return a first-order formula obtained from this formula where all
            the free occurrences of each variable v that appears in the
            dictionary substitution_map are replaced with the term
            substitution_map[v] """
        for variable in substitution_map:
            assert is_variable(variable) and \
                   type(substitution_map[variable]) is Term
        # Task 9.2

    def substitute_constants(self, substitution_map):
        """ Return a first-order formula obtained from this formula where all
            the occurrences of each constant c that appears in the dictionary
            substitution_map are replaced with the term substitution_map[v] """
        for constant in substitution_map:
            assert is_constant(constant) and \
                   type(substitution_map[constant]) is Term
        # Ex12

    def propositional_skeleton(self):
        """ Return a PropositionalFormula that is the skeleton of this one.
            The variables in the propositional formula will have the names
            z1,z2,... (obtained by calling next(fresh_variable_name_generator)),
            starting from left to right """
        # Task 9.5

if __name__ == '__main__':
    args = Term('plus' , [Term('s', [Term('x')]), Term('y')])
    print(args)
    a = args.variables()
    print(a)
    # eq = Formula('=', Term('x'), Term('x'))
    # print(eq)
    # q = Formula('A', 'x', eq)
    # print(q)
    #e
    # f = Formula('F', [args])
    # print(f) 333