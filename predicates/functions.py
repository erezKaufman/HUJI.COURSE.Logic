""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/functions.py """

from predicates.syntax import *
from predicates.semantics import *
from predicates.util import *

zs_dict = {}


def replace_functions_with_relations_in_model(model: Model):
    """ Return a new model obtained from the given model by replacing every
        function meaning with the corresponding relation meaning (i.e.,
        (x1,...,xn) is in the meaning if and only if x1 is the output of the
        function meaning for the arguments x2,...,xn), assigned to a relation
        with the same name as the function, except that the first letter is
        capitalized """
    assert type(model) is Model
    new_meaning = {}
    for func in model.meaning:
        if is_function(func):
            # new_func = func # makes the first letter capital
            new_func = "".join(c.upper() if i == 0  else c for i, c in enumerate(func))
            realtions = set()
            for key in model.meaning[func]:
                new_pair = []
                new_pair.append(model.meaning[func][key])
                for value in key:
                    new_pair.append(value)
                realtions.add(tuple(new_pair))
            new_meaning[new_func] = realtions
        else:
            new_meaning[func] = model.meaning[func]
    return Model(model.universe, new_meaning)
    # Task 8.2


def replace_relations_with_functions_in_model(model: Model, original_functions: set()):
    def check_for_valid_number_of_vals():
        len_of_vals = len(val) - 1
        return len(values) == 2 ** len_of_vals

    """ Return a new model original_model with function names
        original_functions such that:
        model == replace_functions_with_relations_in_model(original_model)
        or None if no such original_model exists """
    assert type(model) is Model
    new_meaning = {}
    for key, values in model.meaning.items():

        temp_key = key[0].lower() + key[1:]
        if temp_key in original_functions:
            function_dict = {}
            for val in values:

                if not check_for_valid_number_of_vals():
                    return None
                function_dict[(val[1:])] = val[0]
            new_meaning[temp_key] = function_dict
        else:
            new_meaning[key] = values
    new_model = Model(model.universe, new_meaning)
    return new_model


def compile_term(term):
    def compile_term_helper(term: Term, z_list: list):
        """

        :param term: the term to process
        :param z_list:  our list of formula's to update
        :param map: a mapping between previously created var's to their respective terms
        """
        if is_constant(term.root) or is_variable(term.root):
            return

        for arg in term.arguments:
            compile_term_helper(arg, z_list)

        if is_function(term.root):
            var = next(fresh_variable_name_generator)
            new_args = []  # holds the new args for this trem, if one of the args should be z_i append that
            for arg in term.arguments:  # iterate over all term's args
                if is_function(arg.root):
                    if arg in zs_dict.keys():  # it's possible we already added this var , if so
                        new_args.append(zs_dict[arg])  # just append it!
                else:
                    new_args.append(arg)  # this is a new arg for a var, append it

            result = Formula('=', Term(var), Term(term.root, new_args))
            z_list.append(result)
            zs_dict[term] = Term(var)

    """ Return a list of steps that result from compiling the given term,
        whose root is a function invocation (possibly with nested function
        invocations down the term tree). Each of the returned steps is a
        Formula of the form y=f(x1,...,xk), where the y is a new variable name
        obtained by calling next(fresh_variable_name_generator) (you may assume
        that such variables do not occur in the given term), f is a
        single function invocation, and each of the xi is either a constant or
        a variable. The steps should be ordered left-to-right between the
        arguments, and within each argument, the computation of a variable
        value should precede its usage. The left-hand-side variable of the last
        step should evaluate to the value of the given term """
    assert type(term) is Term and is_function(term.root)
    z_list = []
    # map = {}
    compile_term_helper(term, z_list)
    return z_list
    # Task 8.4


def replace_functions_with_relations_in_formula(formula: Formula):
    def make_func_to_relation(function: Term, new_var):
        """
        help method for 'create_valid_formula'. it's purpose is to get a function and return a relation in the
        form of Formula object, with the new_var as it's first variable
        :param function: Term object of the formula
        :param new_var:
        :return:
        """
        assert type(function) is Term
        relation_name = function.root[0].upper() + function.root[1:]
        new_args = [new_var] + function.arguments
        return Formula(relation_name, new_args)

    def create_valid_formula(sequences):
        """
        the help method is called from 'replace_functions_with_relations_in_formula' itself. it receives lit of
        sequences that from which we will build our new Formula
        :param sequences:
        :return:
        """
        print(sequences)
        if len(sequences) == 1:
            return sequences[0]

        if is_equality(sequences[0].root):
            new_var = sequences[0].first

            if is_function(sequences[0].second.root):
                new_relation = make_func_to_relation(sequences[0].second, new_var)

            else:
                return sequences[0]
            sequence_formula = Formula('->', new_relation, create_valid_formula(sequences[1:]))
            return Formula('A', new_var.root, sequence_formula)
        else:
            return sequences[0]

    def appeand_to_sequence(formula, helper_sequence):
        if is_function(formula.root):
            term_list = compile_term(formula)
            helper_sequence = helper_sequence + term_list

            term_list = helper_sequence[-1].first
            return term_list, helper_sequence
        else:
            return formula, helper_sequence

    def rfwrif_helper(temp_formula: Formula):
        """

        :param temp_formula:
        :return:
        """
        helper_sequence = []
        if is_relation(temp_formula.root):
            new_relation_args = []  # create new list for new arguments of the relations
            for arg in temp_formula.arguments:
                term = arg
                # if the root is form of a function, we will go on recursion on it with compile_term
                term, helper_sequence = appeand_to_sequence(arg, helper_sequence)

                new_relation_args.append(term)  # R(f(g(h(x))),y,3) = > R(z3,y,3)
            helper_sequence.append(Formula(temp_formula.root, new_relation_args))

        elif is_equality(temp_formula.root):  # Populate self.first and self.second # b=f(a)
            term_first, helper_sequence = appeand_to_sequence(temp_formula.first, helper_sequence)  # b
            term_second, helper_sequence = appeand_to_sequence(temp_formula.second, helper_sequence)  # f(a) = z1
            helper_sequence.append(Formula(temp_formula.root, term_first, term_second))  # b=z1

        elif is_quantifier(temp_formula.root):  # Populate self.variable and self.predicate

            helper_sequence = helper_sequence + rfwrif_helper(temp_formula.predicate)
            helper_sequence.append(Formula(temp_formula.root, temp_formula.variable, helper_sequence[-1]))
        elif is_unary(temp_formula.root):  # Populate self.first
            helper_sequence = helper_sequence + rfwrif_helper(temp_formula.second)
            helper_sequence.append(Formula(temp_formula.root, helper_sequence[-1]))
        else:  # Populate self.first and self.second
            helper_sequence = helper_sequence + rfwrif_helper(temp_formula.first)
            first_arg = helper_sequence[-1]
            helper_sequence = helper_sequence + rfwrif_helper(temp_formula.second)
            second_arg = helper_sequence[-1]
            helper_sequence.append(Formula(temp_formula.root, first_arg, second_arg))
        return helper_sequence

    """ Return a function-free analog of the given formula. Every k-ary
    function that is used in the given formula should be replaced with a
    k+1-ary relation with the same name except that the first letter is
    capitalized (e.g., the function plus(x,y) should be replaced with the
    relation Plus(z,x,y) that stands for z=plus(x,y)). (You may assume
    that such relation names do not occur in the given formula, which
    furthermore does not contain any variables names starting with z.) The
    returned formula need only be equivalent to the given formula for
    models where each new relations encodes a function, i.e., is guaranteed
    to have single possible value for the first relation argument for every
    k-tuple of the other arguments """
    assert type(formula) is Formula

    list_of_sequences = rfwrif_helper(formula)
    # print(zs_dict)
    return create_valid_formula(list_of_sequences)


if __name__ == '__main__':
    # print(replace_functions_with_relations_in_formula(Formula.parse('R(f(g(x)),h(2,y),3)')))
    print(replace_functions_with_relations_in_formula(Formula.parse('Ax[(Ey[f(y)=x]->GT(x,a))]')))
    # print(replace_functions_with_relations_in_formula(Formula.parse('GT(f(a),g(b))')))
    # replace_functions_with_relations_in_formula(Formula.parse('R(3)'))


# ∀z1[(G(z1, x)→∀z2[(F(z2, z1)→∀z3[(H(z3, 2, y)→R(z2, z3, 3))])])]


def replace_functions_with_relations_in_formulae(formulae):
    """ Return a list of function-free formulae (as strings) that is equivalent
        to the given formulae list (also of strings) that may contain function
        invocations. This equivalence is in the following sense:
        for every model of the given formulae,
        replace_functions_with_relations_in_model(model) should be a model
        of the returned formulae, and for every model of the returned formulae,
        replace_relations_with_functions_in_model(model) should be a model
        of the given formulae. Every k-ary function that is used in the given
        formulae should be replaced with a k+1-ary relation with the same name
        except that the first letter is capitalized (e.g., the function
        plus(x,y) should be replaced with the relation Plus(z,x,y) that stands
        for z=plus(x,y)). (You may assume that such relation names do not occur
        in the given formulae, which furthermore does not contain any variables
        names starting with z.) The returned list should have one formula for
        each formula in the given list, as well as one additional formula for
        every relation that replaces a function name from the given list """
    for formula in formulae:
        assert type(formula) is str
        # task 8.6


def replace_equality_with_SAME(formulae):
    """ Return a list of equality-free formulae (as strings) that is equivalent
        to the given formulae list (also of strings) that may contain the
        equality symbol. Every occurrence of equality should be replaced with a
        matching instantiation of the relation SAME, which you may assume
        does not occur in the given formulae. You may assume that the given
        formulae do not contain any function invocations. The returned list
        should have one formula for each formula in the given list, as well as
        additional formulae that ensure that SAME is reflexive, symmetric,
        transitive, and respected by all relations in the given formulae """
    for formula in formulae:
        assert type(formula) is str
        # Task 8.7


def add_SAME_as_equality(model):
    """ Return a new model obtained from the given model by adding the relation
        SAME that behaves like equality """
    assert type(model) is Model
    # Task 8.8


def make_equality_as_SAME(model):
    """ Return a new model where equality is made to coincide with the
        reflexive, symmetric, transitive, and respected by all relations,
        relation SAME in the the given model. The requirement is that for every
        model and every list formulae_list, if we take
        new_formulae=replace_equality_with_SAME(formulae) and
        new_model=make_equality_as_SAME(model) then model is a valid model
        of new_formulae if and only if new_model is a valid model of formulae.
        The universe of the returned model should correspond to the equivalence
        classes of the SAME relation in the given model. You may assume that
        there are no function meanings in the given model """
    assert type(model) is Model
    # Task 8.9
