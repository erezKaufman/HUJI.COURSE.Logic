""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/semantics.py """

from predicates.syntax import *

class Model:
    """ A model for first-order formulae: contains a universe - a set of
        elements, and a dictionary that maps every constant name to an element,
        every k-ary relation name to a set of k-tuples of elements, and every
        k-ary function name to a map from k-tuples of elements to an element """

    def __init__(self, universe, meaning):
        assert type(universe) is set
        assert type(meaning) is dict
        self.universe = universe
        self.meaning = meaning

    def __repr__(self):
        return 'Universe=' + str(self.universe) + '; Meaning=' + str(self.meaning)
        
    def evaluate_term(self, term, assignment={}):
        """ Return the value of the given term in this model, where variables   
            get their value from the given assignment """
        assert term.variables().issubset(assignment.keys())
        if is_constant(term.root): # if the term is a constant
            return self.meaning[term.root]
        elif is_variable(term.root): # if the term is a variable
            return assignment[term.root]
        else: # else the term is a function
            eval_args = []
            for arg in term.arguments:
                eval_args.append(self.evaluate_term(arg,assignment))
            eval_args = tuple(eval_args)
            return self.meaning[term.root][eval_args]




    def evaluate_formula(self, formula, assignment={}):
        """ Return the value of the given formula in this model, where
            variables that are free in the formula get their values from the
            given assignment """
        assert formula.free_variables().issubset(assignment.keys())
        # def eval_formula_helper(str):

        #
        #     # if there is a left parentheses it means that we are having an operator that is enclosed by parenthesis
        #     if is_left_parenthese(Term.str[0]):
        #         Term.eat()  # eat left parentheses
        #         first, str = Formula.parse_prefix(str)  # take first formula of the operator
        #         root = switch_root_to_str(str[0])  # take the root
        #         Term.eat()  # eat the root
        #         second, str = Formula.parse_prefix(str)  # take second formula of the operator
        #         Term.eat()  # eat right parentheses
        #         return
        #         # if first letter is a quantifier ('A' or 'E')
        #     elif is_quantifier(str[0]):
        #         root = str[0]  # take the quantifier as root
        #         Term.eat()  # eat the root ( quantifier)
        #         first = Term.get_whole_name()  # take the name of the variable
        #         Term.eat()  # eat the left bracket
        #         second, str = Formula.parse_prefix(str)  # take the formula
        #         Term.eat()  # eat the right bracket
        #
        #     # if first letter is a relation (starts with capital letter)
        #     elif is_relation(str[0]):
        #         root = Term.get_whole_name()  # take the name of the relation
        #         first = []
        #         Term.eat()  # eat left parentheses
        #
        #         # if we didn't find closing parenthesis - than there must be at least one Term inside the parenthesis.
        #         # take it.
        #         if not is_right_parenthese(str[0]):
        #             term_obj, str = Term.parse_prefix(str)
        #             first.append(term_obj)
        #
        #         # while there is a comma, take the next term
        #         while is_comma(str[0]):
        #             Term.eat()  # eat left parentheses
        #             term_obj, str = Term.parse_prefix(str)
        #             first.append(term_obj)
        #         Term.eat()  # eat right parentheses
        #
        #     # else , it is an operator
        #     else:
        #
        #         # if it's an unary operator
        #         if is_unary(str[0]):
        #             root = str[0]
        #             Term.eat()
        #             first, str = Formula.parse_prefix(str)
        #
        #         # else , the operator is binary or equaluty
        #         else:
        #             first, str = Term.parse_prefix(str)
        #             # if it's a binary operator
        #             if is_binary(str[0]):
        #                 root = str[0:2]
        #                 Term.eat()
        #
        #             # if it's an equal operator
        #             else:
        #                 root = str[0]
        #             Term.eat()
        #             second, str = Term.parse_prefix(str)
        #     returned_formula = Formula(root, first, second)
        #     return returned_formula, str
        # # Term.str = replace_string(s)  # replace operators with more than one letter to be one letter
        # str = replace_string(str(formula))
        # eval_formula_helper(str)
        if is_equality(formula.root):
            first_term = self.evaluate_term(formula.first,assignment)
            second_term = self.evaluate_term(formula.second,assignment)
            return first_term == second_term

        elif is_quantifier(formula.root):
            pass

        elif is_relation(formula.root):
            eval_args = set()
            for arg in formula.arguments:
                new_tuple = tuple(self.evaluate_term(arg,assignment))
                eval_args.add(new_tuple)
            # eval_args = tuple(eval_args)
            return self.meaning[formula.root] == eval_args

        elif is_unary(formula.root):
            return not self.evaluate_formula(formula.first,assignment)
        elif is_binary(formula.root):
            first_term = self.evaluate_formula(formula.first,assignment)
            second_term = self.evaluate_formula(formula.second,assignment)
            if formula.root == '->':
                return not first_term or second_term
            elif formula.root == '|':
                return first_term or second_term
            elif formula.root == '&':
                return first_term and second_term

    def is_model_of(self, formulae_repr):
        """ Return whether self a model of the formulae represented by the
            given list of strings. For this to be true, each of the formulae
            must be satisfied, if the formula has free variables, then it must
            be satisfied for every assignment of elements of the universe to
            the free variables """
        # Task 7.9
