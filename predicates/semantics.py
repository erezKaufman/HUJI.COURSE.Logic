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
        # Task 7.8

    def is_model_of(self, formulae_repr):
        """ Return whether self a model of the formulae represented by the
            given list of strings. For this to be true, each of the formulae
            must be satisfied, if the formula has free variables, then it must
            be satisfied for every assignment of elements of the universe to
            the free variables """
        # Task 7.9
