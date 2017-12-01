""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/semantics.py """

from propositions.syntax import *
import itertools
from propositions.proofs import *



def evaluate(formula, model):
    """ Return the truth value of the given formula in the given model """
    if is_variable(formula.root):
        return model[formula.root]
    elif is_constant(formula.root):
        return True if formula.root == TRUE_IN_FORM else False
    elif is_unary(formula.root):
        return not evaluate(formula.first, model)
    elif is_binary(formula.root):
        if formula.root == AND_OPERATOR:
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif formula.root == OR_OPERATOR:
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif formula.root == IMPLICATION_OPERATOR:
            return not evaluate(formula.first,model) or evaluate(formula.second,model)
        elif formula.root == BICONDITIONAL_OPERATOR:
            first = evaluate(formula.first,model)
            second = evaluate(formula.second,model)
            return (first and second) or (not first and not second)
        elif formula.root == NAND_OPERATOR:
            first = evaluate(formula.first, model)
            second = evaluate(formula.second, model)
            return not (first and second)
        elif formula.root == NOR_OPERATOR:
            first = evaluate(formula.first, model)
            second = evaluate(formula.second, model)
            return not (first or second)
    else:
        return evaluate(formula.second, model) if evaluate(formula.first, model) else evaluate(formula.third,model)


def create_model(variables, n, return_dict):
    """ help function for recursive calls """
    if n == len(variables):
        return_list.append(return_dict.copy())
        return None

    return_dict[variables[n]] = False
    create_model(variables, n + 1, return_dict)

    return_dict[variables[n]] = True
    create_model(variables, n + 1, return_dict)


def all_models(variables):
    """ Return an iterator over all possible models over the variables in the
        given list of variables. The order of the models is lexicographic
        according to the order of the variables in the given list, where False
        precedes True """
    return_list.clear()
    create_model(variables, 0, {})
    for dict in return_list:
        yield dict

    return_list.clear()


def truth_values(formula, models):
    """ Return a list of the truth values of the given formula in each model
        in the given list of models """
    truth_list = []
    for model in models:
        f = evaluate(formula, model)
        truth_list.append(f)

    return truth_list


def is_tautology(formula):
    """ Return whether the given formula is a tautology """
    # truth_values(formula, all_models(list(formula.variables())))
    truth_list = truth_values(formula, all_models(list(formula.variables())))
    if False in truth_list:  # or set(truth_list)
        return False
    return True


def return_boolean(bool_val):
    """ help function to return string value for the boolean"""
    return TRUE_IN_FORM if bool_val is True else FALSE_IN_FORM


def print_truth_table(formula):
    """ Print the truth table of the given formula """
    variables = sorted(list(formula.variables()))  # brings back the list of variables in the formula

    truth_generator1 = all_models(variables)  # brings back a generator for the truth model
    truth_generator1, truth_generator2 = itertools.tee(truth_generator1)

    truth_list = truth_values(formula, truth_generator2)  # brings back the list of the varibale's truth table
    table_to_print = [OR_OPERATOR] * (len(truth_list) + 2)
    formula_string = formula.infix()

    for var in variables:  # run on the first two lines and draw the basic of the table
        table_to_print[0] = table_to_print[0] + ' ' + str(var) + ' ' + OR_OPERATOR
        table_to_print[1] = table_to_print[1] + '-' * (len(var) + 2) + OR_OPERATOR
    # print the last column in both the first and second lines
    table_to_print[0] = table_to_print[0] + ' ' + formula_string + ' ' + OR_OPERATOR
    table_to_print[1] = table_to_print[1] + '-' * (len(formula_string) + 2) + OR_OPERATOR
    counter = 2

    for model in truth_generator1:  # run on the number of possible models for the formula
        for var in sorted(sorted(variables)):
            table_to_print[counter] = table_to_print[counter] + ' ' + return_boolean(model[var]) + ' ' * len(
                var) + OR_OPERATOR

        table_to_print[counter] = table_to_print[counter] + ' ' + return_boolean(truth_list[counter - 2]) + ' ' * (len(
            formula_string)) + OR_OPERATOR
        counter += 1

    for line in table_to_print:
        print(line)


def check_truth(key, value):
    """ helper function to return the form of the variable"""
    if value:
        return key
    else:
        return NEGATE_OPERATOR + key


def synthesize_for_model_helper(model, formula_string):
    """ help function that returns a prefix presentation of the formula that fits the model"""
    formula_string += AND_OPERATOR * (len(model) - 1)
    for key, value in model.items():
        if len(model) == 1:
            return check_truth(key, value)
        formula_string += check_truth(key, value)
    return formula_string


def synthesize_for_model(model):
    """ Return a propositional formula that evaluates to True in the given
        model, and to False in any other model over the same variables """

    return Formula.from_prefix(synthesize_for_model_helper(model, ''))


def return_form_with_const(boolean, formula):
    """ help function to return a formula with a bool sign similar to the truth values in the truth list"""
    bool = TRUE_IN_FORM if boolean else FALSE_IN_FORM
    return AND_OPERATOR + bool + formula


def synthesize(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models """
    formula_list = []
    models_copy = []
    returning_formula = ''
    for model in models:
        models_copy.append(model)
        formula_to_add = synthesize_for_model(model)
        formula_list.append(formula_to_add.prefix())
        # print(model_to_add)
    returning_formula += OR_OPERATOR * (len(formula_list) - 1)
    for val in range(0, len(values)):
        returning_formula += return_form_with_const(values[val], formula_list[val])
    return Formula.from_prefix(returning_formula)


def evaluate_inference(rule, model):
    """ Return whether the given inference rule holds in the given model """
    for ass in rule.assumptions:
        if not evaluate(ass,model): #if the model is false then the rule holds
            return True
    # if Arrived here then all assumptions are True, check if conclusion is true
    return evaluate(rule.conclusion, model)


def is_tautological_inference(rule):
    """ Return whether the given inference rule is a semantically correct
        implication of its assumptions """
    list_of_evaluate_interface = [evaluate_inference(rule,a) for a in list(all_models(list(rule.variables())))]
    return False if False in list_of_evaluate_interface else True

