""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/semantics.py """

from predicates.syntax import *
from itertools import product


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
        if is_constant(term.root):  # if the term is a constant
            return self.meaning[term.root]
        elif is_variable(term.root):  # if the term is a variable
            return assignment[term.root]
        else:  # else the term is a function
            eval_args = []
            for arg in term.arguments:
                eval_args.append(self.evaluate_term(arg, assignment))
            eval_args = tuple(eval_args)
            return self.meaning[term.root][eval_args]

    def evaluate_formula(self, formula, assignment={}):
        """ Return the value of the given formula in this model, where
            variables that are free in the formula get their values from the
            given assignment """
        assert formula.free_variables().issubset(assignment.keys())

        if is_equality(formula.root):
            first_term = self.evaluate_term(formula.first, assignment)
            second_term = self.evaluate_term(formula.second, assignment)
            return first_term == second_term

        elif is_quantifier(formula.root):
            frees_vars = formula.free_variables()  # TODO how do the free var's go into the picture?
            results = []
            for elem in self.universe:
                assignment[formula.variable] = elem  # assigns cur universe element to variable
                results.append(self.evaluate_formula(formula.predicate, assignment))
            if formula.root == 'A':
                return False if False in results else True
            elif formula.root == 'E':
                return True if True in results else False

        elif is_relation(formula.root):
            # eval_args = set()
            new_tuple = []
            for arg in formula.arguments:
                new_tuple.append(self.evaluate_term(arg, assignment))
            # eval_args.add(tuple(new_tuple))
            eval_args = tuple(new_tuple)
            return eval_args in self.meaning[formula.root]

        elif is_unary(formula.root):
            return not self.evaluate_formula(formula.first, assignment)

        elif is_binary(formula.root):
            first_term = self.evaluate_formula(formula.first, assignment)
            second_term = self.evaluate_formula(formula.second, assignment)
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
        truth_list = []
        for formula in formulae_repr:
            formula = Formula.parse(formula)
            free_vars = formula.free_variables()
            if free_vars != set():
                possibilities = self.create_all_subsets(free_vars)
                for ass in possibilities:
                    truth_list.append(self.evaluate_formula(formula, ass))

        return False if False in truth_list else True

    def create_all_subsets(self, vars):
        iter_sets = product(self.universe, repeat=len(vars))
        list_to_return = []
        for arg in iter_sets:
            temp_dict = {}
            for i, var in enumerate(vars):
                temp_dict[var] = arg[i]
            list_to_return.append(temp_dict)

        return list_to_return
