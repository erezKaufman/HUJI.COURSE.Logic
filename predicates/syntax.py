""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/syntax.py """

from propositions.syntax import Formula as PropositionalFormula
from predicates.util import *
import copy

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

        arguments = None
        Term.str = s
        term_name = Term.get_whole_name()
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
        returned_term = Term(term_name, arguments)
        return returned_term, Term.str

    @staticmethod
    def get_whole_name():
        retruned_name = ''
        while Term.str != '' and Term.str[0].isalnum():
            retruned_name += Term.str[0]
            Term.eat()
        return retruned_name

    @staticmethod
    def parse(s):
        """ Return a term parsed from its given string representation """
        Term.str = s
        new_term = None
        while Term.str != '':
            new_term, Term.str = Term.parse_prefix(Term.str)
        return new_term



    def substitute(self, substitution_map):
        """ Return a term obtained from this term where all the occurrences of
            each constant name or variable name element_name that appears as a
            key in the dictionary substitution_map are replaced with the term
            substitution_map[element_name] """
        for element_name in substitution_map:
            assert (is_constant(element_name) or is_variable(element_name)) and \
                   type(substitution_map[element_name]) is Term

        if is_constant(self.root) or is_variable(self.root): # we need to to deal only with the root
            if self.root in substitution_map.keys():
                return substitution_map[self.root] # change it with it is in the map
            else: return Term(self.root) # else return it as is

        else:
            assert is_function(self.root) # we have a function
            if self.root in substitution_map.keys():
                root = substitution_map[self.root] # update the root if it is in map
            else:
                root = self.root # else, leave it as it is, without changing it to Term
            args = [] # this is our args
            for index, arg in enumerate(self.arguments): # for every arg, switch it with it's substitute
                args.append(arg.substitute(substitution_map)) # recursive call to substitute
            return Term(root,args)
        # Task 9.1


    def variables(self):
        def variables_helper(vars:set):
            if is_variable(self.root):
                vars.add(self.root) # add it
            elif is_constant(self.root):
                return # we don't care if it's a constant
            elif is_function(self.root):
                for arg in self.arguments: # for each Term take the term's variables and update over_all var's
                    vars.update(arg.variables())
            return

        """ Return the set of variables in this term """
        vars = set()  # holds the var set for the Formula
        variables_helper(vars)  # updates formula's set
        return vars
        # Task 7.5

    def functions(self):
        def functions_helper(returned_set: set):
            if is_variable(self.root) or is_constant(self.root):
                return  # we don't care if it's a constant or a variable
            elif is_function(self.root):
                returned_set.add((self.root,len(self.arguments)))
                for arg in self.arguments:  # for each Term take the term's variables and update over_all var's
                    returned_set.update(arg.functions())
            return

        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this term """
        # Task 8.1
        returned_set = set()
        functions_helper(returned_set)
        return returned_set


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

        Term.str = replace_string(s) # replace operators with more than one letter to be one letter
        second = None

        # if there is a left parentheses it means that we are having an operator that is enclosed by parenthesis
        if is_left_parenthese(Term.str[0]):
            Term.eat()  # eat left parentheses
            first, Term.str = Formula.parse_prefix(Term.str) # take first formula of the operator
            root = switch_root_to_str(Term.str[0]) # take the root
            Term.eat() # eat the root
            second, Term.str = Formula.parse_prefix(Term.str) # take second formula of the operator
            Term.eat()  # eat right parentheses

        # if first letter is a quantifier ('A' or 'E')
        elif is_quantifier(Term.str[0]):
            root = Term.str[0] # take the quantifier as root
            Term.eat()  # eat the root ( quantifier)
            first = Term.get_whole_name()  # take the name of the variable
            Term.eat()  # eat the left bracket
            second, Term.str = Formula.parse_prefix(Term.str) # take the formula
            Term.eat()  # eat the right bracket

        # if first letter is a relation (starts with capital letter)
        elif is_relation(Term.str[0]):
            root = Term.get_whole_name() # take the name of the relation
            first = []
            Term.eat()  # eat left parentheses

            # if we didn't find closing parenthesis - than there must be at least one Term inside the parenthesis.
            # take it.
            if not is_right_parenthese(Term.str[0]):
                term_obj, Term.str = Term.parse_prefix(Term.str)
                first.append(term_obj)

            # while there is a comma, take the next term
            while is_comma(Term.str[0]):
                Term.eat()  # eat left parentheses
                term_obj, Term.str = Term.parse_prefix(Term.str)
                first.append(term_obj)
            Term.eat()  # eat right parentheses

        # else , it is an operator
        else:

            # if it's an unary operator
            if is_unary(Term.str[0]):
                root = Term.str[0]
                Term.eat()
                first, Term.str = Formula.parse_prefix(Term.str)

            # else , the operator is binary or equaluty
            else:
                first, Term.str = Term.parse_prefix(Term.str)
                # if it's a binary operator
                if is_binary(Term.str[0]):
                    root = Term.str[0:2]
                    Term.eat()

                # if it's an equal operator
                else:
                    root = Term.str[0]
                Term.eat()
                second, Term.str = Term.parse_prefix(Term.str)
        returned_formula = Formula(root, first, second)
        return returned_formula, Term.str

    @staticmethod
    def parse(s):
        """ Return a first-order formula parsed from its given string
            representation """
        Term.str = s
        new_Formula = None
        while Term.str != '':
            new_Formula, Term.str = Formula.parse_prefix(Term.str)
        return new_Formula
        # Task 7.4.2

    def subsitute_helper(self, inner_subsitution_map,is_instantiation):
        """
        help method for substitut method in Formula class. it calls recursively to terms of the formula or deeper
        formulas in the tree, while removing non-free variables that might appear in the substitution_map
        :param inner_subsitution_map:
        :param is_instantiation: flag to be raised when the method is called from 'instantiate_formula' method
        :return:
        """
        second = None
        if is_relation(self.root):  # Populate self.root and self.arguments
            first = []
            for x in self.arguments:
                first.append(x.substitute(inner_subsitution_map))

        elif is_equality(self.root):  # Populate self.first and self.second
            first = self.first.substitute(inner_subsitution_map)
            second = self.second.substitute(inner_subsitution_map)

        elif is_quantifier(self.root):  # Populate self.variable and self.predicate
            # if the variable appears in the quantifier, delete it from the   dictionary for this part of the tree
            if self.variable in inner_subsitution_map:
                # if we entered the method through 'instantiate_formula', then we want to keep the
                if is_instantiation:
                    first = inner_subsitution_map[self.variable].root

                else:
                    del inner_subsitution_map[self.variable]
                    first = self.variable
            else:
                first = self.variable
            second = self.predicate.subsitute_helper(inner_subsitution_map,is_instantiation)
        elif is_unary(self.root):  # Populate self.first
            first = self.first.subsitute_helper(inner_subsitution_map,is_instantiation)
        else:  # Populate self.first and self.second
            first = self.first.subsitute_helper(inner_subsitution_map,is_instantiation)
            second = self.second.subsitute_helper(inner_subsitution_map,is_instantiation)
        return Formula(self.root, first, second)

    def substitute(self, substitution_map):

        """ Return a first-order formula obtained from this formula where all
            occurrences of each constant name element_name and all *free*
            occurrences of each variable name element_name for element_name
            that appears as a key in the dictionary substitution_map are
            replaced with substitution_map[element_name] """
        for element_name in substitution_map:
            assert (is_constant(element_name) or is_variable(element_name)) and \
                   type(substitution_map[element_name]) is Term
        return self.subsitute_helper(copy.deepcopy(substitution_map),False)


    def free_variables_helper(self ,free:set, non_free=set()):
        if is_variable(self.root):
            if self.root not in non_free: # this var was not referenced before
                free.add(self.root) # adds var

        if is_constant(self.root):
            return

        elif is_unary(self.root):
            self.first.free_variables_helper(free, non_free) # recursive call on first

        elif is_equality(self.root):
            self.get_Term_frees(self.first, free, non_free) #uppends all first term's free var's
            self.get_Term_frees(self.second, free, non_free) #uppends all second term's free var's

        elif is_relation(self.root):
            for arg in self.arguments:
                self.get_Term_frees(arg, free, non_free) # for each argument (which is var) uppend all term's free's

        elif is_quantifier(self.root):
            non_free.add(self.variable) # add var to non_free
            self.predicate.free_variables_helper(free, non_free) #call helper with predicate values
            non_free.remove(self.variable) # the added var to non_free no longer affects rest of formula

        elif is_binary(self.root):
            self.first.free_variables_helper(free, non_free) # call helper with first
            self.second.free_variables_helper(free, non_free) # call helper with second

    def get_Term_frees(self, arg, free, non_free):
        args_vars = arg.variables() # get term's variables
        if args_vars != set(): # the set is not empty
            for var in args_vars:
                if var not in non_free and is_variable(var): # if it wasnt refrenced and is a var add it
                    free.add(var)

    def free_variables(self):
        """ Return the set of variables that are free in this formula """

        free_vars = set()
        self.free_variables_helper(free_vars)
        return free_vars
        # Task 7.6

    def functions(self):
        def functions_helper(returned_set : set()):
            if is_relation(self.root):  # Populate self.root and self.arguments
                for arg in self.arguments:
                    returned_set.update(arg.functions())

            elif is_equality(self.root):  # Populate self.first and self.second
                returned_set.update(self.first.functions())
                returned_set.update(self.second.functions())

            elif is_quantifier(self.root): # Populate self.variable and self.predicate
                returned_set.update(self.predicate.functions())

            elif is_unary(self.root): # Populate self.first
                returned_set.update(self.first.functions())

            else: # Populate self.first and self.second
                returned_set.update(self.first.functions())
                returned_set.update(self.second.functions())

            return

        """ Return a set of pairs (function_name, arity) for all function names
                    that appear in this formula """
        returned_set = set()
        functions_helper(returned_set)
        return  returned_set
        # Task 8.1.2

    def relations(self):
        """ Return a set of pairs (relation_name, arity) for all relation names
            that appear in this formula """
        def functions_helper(returned_set : set()):
            if is_relation(self.root):  # Populate self.root and self.arguments
                returned_set.add((self.root,len(self.arguments)))

            elif is_equality(self.root):  # Populate self.first and self.second
                return
            elif is_quantifier(self.root): # Populate self.variable and self.predicate
                returned_set.update(self.predicate.relations())

            elif is_unary(self.root): # Populate self.first
                returned_set.update(self.first.relations())

            else: # Populate self.first and self.second
                returned_set.update(self.first.relations())
                returned_set.update(self.second.relations())
            return

        """ Return a set of pairs (function_name, arity) for all function names
                    that appear in this formula """
        returned_set = set()
        functions_helper(returned_set)
        return returned_set

        # Ex12

    def propositional_skeleton(self):
        """ Return a PropositionalFormula that is the skeleton of this one.
            The variables in the propositional formula will have the names
            z1,z2,... (obtained by calling next(fresh_variable_name_generator)),
            starting from left to right """
        # Task 9.5


# def subsitute_helper(self, inner_subsitution_map, is_instance):
#     """
#     help method for substitut method in Formula class. it calls recursively to terms of the formula or deeper
#     formulas in the tree, while removing non-free variables that might appear in the substitution_map
#     :param free_vars_list:
#     :return:
#     """
#     second = None
#     if is_relation(self.root):  # Populate self.root and self.arguments
#         first = []
#         for x in self.arguments:
#             first.append(x.substitute(inner_subsitution_map))
#
#     elif is_equality(self.root):  # Populate self.first and self.second
#         first = self.first.substitute(inner_subsitution_map)
#         second = self.second.substitute(inner_subsitution_map)
#
#     elif is_quantifier(self.root):  # Populate self.variable and self.predicate
#         if self.variable in inner_subsitution_map:  # if the variable appears in the quantifier, delete it from the
#             #  dictionary for this part of the tree
#             del inner_subsitution_map[self.variable]
#         first = self.variable
#         second = self.predicate.substitute(inner_subsitution_map)
#     elif is_unary(self.root):  # Populate self.first
#         first = self.first.substitute(inner_subsitution_map)
#     else:  # Populate self.first and self.second
#         first = self.first.substitute(inner_subsitution_map)
#         second = self.second.substitute(inner_subsitution_map)
#     return Formula(self.root, first, second)