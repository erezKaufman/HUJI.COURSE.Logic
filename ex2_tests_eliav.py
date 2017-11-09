""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/semantics.py """


""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/syntax.py """


def is_variable(s):
    """ Is s an atomic proposition?  """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())


def is_unary(s):
    """ Is s a unary operator? """
    return s == '~'


def is_binary(s):
    """ Is s a binary operator? """
    return s == '&' or s == '|'


def is_constant(s):
    """ Is s a constant? """
    return s == 'T' or s == 'F'


def is_parentheses(s):
    return s == '(' or s == ')'


class Formula:
    """ A Propositional Formula """
    string = ''

    def __init__(self, root, first=None, second=None):
        """ Create a new formula from its root (a string) and, when needed, the
        first and second operands (each of them a Formula).
        - I added to each object a variable of string to save each time the current state of the formula's string """
        if is_constant(root) or is_variable(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __repr__(self):
        return self.infix()

    def __eq__(self, other):
        return self.infix() == other.infix()

    def __ne__(self, other):
        return not self == other

    def infix(self):
        """ Return an infix representation of self """
        if is_constant(self.root) or is_variable(self.root):
            return (self.root)
        elif is_unary(self.root):
            return (self.root) + self.first.infix()

        else:
            return '(' + self.first.infix() + self.root + self.second.infix() + ')'

    @staticmethod
    def from_infix(s):
        """ Return a propositional formula whose infix representation is s """
        Formula.string = s
        if is_constant(s[0]) or is_variable(s[0]):
            #  if the first letter is a variable, we want to check if the next to letters are digits
            return_var = ''
            if len(s) > 1 and s[1].isdigit():
                if len(s) > 2 and s[2].isdigit():
                    Formula.string = s[3:]
                    return_var = s[0:3]
                else:
                    Formula.string = s[2:]
                    return_var = s[0:2]
            else:
                if len(s) > 1:
                    Formula.string = s[1:]
                return_var = s[0]
            return Formula(return_var)
        elif is_unary(s[0]):
            Formula.string = s[1:]
            return Formula(s[0], Formula.from_infix(s[1:]))
        elif is_parentheses(s[0]):
            first = Formula.from_infix(s[1:])
            s = Formula.string
            # remove redundant parentheses
            while is_parentheses(s[0]):
                s = s[1:]
            root = s[0]
            second = Formula.from_infix(s[1:])
            return Formula(root, first, second)

    def prefix(self):
        """ Return a prefix representation of self """
        if is_constant(self.root) or is_variable(self.root):
            return (self.root)
        elif is_unary(self.root):
            return (self.root) + self.first.prefix()

        else:
            return self.root + self.first.prefix() + self.second.prefix()

    @staticmethod
    def from_prefix(s):
        """ Return a propositional formula whose prefix representation is s """
        Formula.string = s
        if is_unary(s[0]):
            Formula.string = s[1:]
            return Formula(s[0], Formula.from_prefix(s[1:]))
        elif is_variable(s[0]) or is_constant(s[0]):
            #  if the first letter is a variable, we want to check if the next to letters are digits
            return_var = ''
            if len(s) > 1 and s[1].isdigit():
                if len(s) > 2 and s[2].isdigit():
                    Formula.string = s[3:]
                    return_var = s[0:3]
                else:
                    Formula.string = s[2:]
                    return_var = s[0:2]
            else:
                if len(s) > 1:
                    Formula.string = s[1:]
                return_var = s[0]
            return Formula(return_var)
        elif is_binary(s[0]):
            root = s[0]
            first = Formula.from_prefix(s[1:])
            s = Formula.string
            second = Formula.from_prefix(s)
            return Formula(root, first, second)

    def variables(self):
        """ Return the set of atomic propositions (variables) used in self """
        return_set = set()
        if is_variable(self.root):
            return {self.root}
        elif is_unary(self.root):
            return_set.update(self.first.variables())
            return return_set
        elif is_constant(self.root):
            return set()
        else:
            return_set.update(self.first.variables())
            return_set.update(self.second.variables())
            return return_set


import itertools

AND_OPERATOR = '&'
return_list = []
symbol_list = ['&', '|', '~']


def evaluate(formula, model):
    """ Return the truth value of the given formula in the given model """
    if is_variable(formula.root):
        return model[formula.root]
    elif is_constant(formula.root):
        return True if formula.root == 'T' else False
    elif is_unary(formula.root):
        return not evaluate(formula.first, model)
    elif is_binary(formula.root):
        if formula.root == AND_OPERATOR:
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        else:
            return evaluate(formula.first, model) or evaluate(formula.second, model)


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
    create_model(variables, 0, {})
    for dict in return_list:
        yield dict

    return_list.clear()


def truth_values(formula, models):
    """ Return a list of the truth values of the given formula in each model
        in the given list of models """
    truth_list = []
    for model in models:
        truth_list.append(evaluate(formula, model))
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
    return 'T' if bool_val is True else 'F'


def print_truth_table(formula):
    """ Print the truth table of the given formula """
    variables = sorted(list(formula.variables()))  # brings back the list of variables in the formula

    truth_generator1 = all_models(variables)  # brings back a generator for the truth model
    truth_generator1, truth_generator2 = itertools.tee(truth_generator1)

    truth_list = truth_values(formula, truth_generator2)  # brings back the list of the varibale's truth table
    table_to_print = ['|'] * (len(truth_list) + 2)
    formula_string = formula.infix()

    for var in variables:  # run on the first two lines and draw the basic of the table
        table_to_print[0] = table_to_print[0] + ' ' + str(var) + ' |'
        table_to_print[1] = table_to_print[1] + '-' * (len(var) + 2) + '|'

    table_to_print[0] = table_to_print[0] + ' ' + formula_string + ' |'
    table_to_print[1] = table_to_print[1] + '-' * (len(formula_string) + 2) + '|'
    counter = 2

    for model in truth_generator1:  # run on the number of possible models for the formula
        for var in sorted(sorted(variables)):
            table_to_print[counter] = table_to_print[counter] + ' ' + return_boolean(model[var]) + ' ' * len(var) + '|'

        table_to_print[counter] = table_to_print[counter] + ' ' + return_boolean(truth_list[counter - 2]) + ' ' * (len(
            formula_string)) + '|'
        counter += 1

    for line in table_to_print:
        print(line)


def check_truth(key, value):
    """ helper function to return the form of the variable"""
    if value:
        return key
    else:
        return '~' + key


def synthesize_for_model_helper(model, formula_string):
    """ help function that returns a prefix presentation of the formula that fits the model"""
    formula_string += '&' * (len(model) - 1)

    for key, value in model.items():
        if len(model) == 1:
            return check_truth(key, value)
        formula_string += check_truth(key, value)
        # if model[var]:
        #     formula_string += var
        # else:
        #     formula_string += '~' + var
    return formula_string


# p: T , q : F , z : T = ((p|q)&z)
def synthesize_for_model(model):
    """ Return a propositional formula that evaluates to True in the given
        model, and to False in any other model over the same variables """

    return Formula.from_prefix(synthesize_for_model_helper(model, ''))


def return_form_with_const(boolean, formula):
    bool = 'T' if boolean else 'F'
    return '&' + bool + formula


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
    returning_formula += '|' * (len(formula_list) - 1)
    for val in range(0, len(values)):
        returning_formula += return_form_with_const(values[val], formula_list[val])
    return Formula.from_prefix(returning_formula)




import random
import sys
from collections import OrderedDict


def task_1(formulas):
    with open('./results/task1_temp', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            _ = formula.split('-')
            formula = _[0]
            formula = Formula.from_infix(formula)
            # Not soo good in security manners..
            model = eval(_[1].replace('\n', ''))
            result.write('(%d) Task_1 testing formula: %s evaluate result: %s\n' % (counter, formula.infix(), evaluate(formula, model)))
            result.write("model %s\n" % (sorted(list(model))))
            result.write("-------------------------------\n")
            counter += 1


def task_2(formulas):
    with open('./results/task2_temp', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            variables = formula.variables()
            result.write('(%d) Task_2 testing formula: %s\n' % (counter, formula.infix()))
            models = sorted(all_models(list(variables)), key=lambda x: sorted(x.items()))
            result.write("all_models: \n")
            for model in models:
                for key, value in sorted(model.items()):
                    result.write(str(key) + '=' + str(value) + ", ")
                result.write('\n')
            result.write("-------------------------------\n")
            counter += 1


def task_3(formulas):
    with open('./results/task3_temp', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            variables = list(formula.variables())
            result.write('(%d) Task_3 testing formula: %s\n' % (counter, formula.infix()))
            result.write("truth_values %s\n" % (str(sorted(truth_values(formula, all_models(variables))))))
            result.write("-------------------------------\n")
            counter += 1


def task_4(formulas):
    with open('./results/task4_temp', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            result.write('(%d) Task_4 testing formula: %s\n' % (counter, formula.infix()))
            result.write("truth_values %s\n" % (str(is_tautology(formula))))
            result.write("-------------------------------\n")
            counter += 1


def task_5(formulas):
    with open('./results/task5_temp', 'w') as result:
        old_target = sys.stdout
        sys.stdout = result
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            result.write('(%d) Task_5 testing formula: %s\n' % (counter, formula.infix()))
            print_truth_table(formula)
            result.write("-------------------------------\n")
            counter += 1
        sys.stdout = old_target


def task_6(formulas):
    with open('./results/task6_temp', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            result.write('(%d) Task_6 testing formula: %s\n' % (counter, formula.infix()))
            models = all_models(list(formula.variables()))
            chosen_model = None
            for model in models:
                if len(model) != 0:
                    chosen_model = model
                    break
            if chosen_model is None:
                counter += 1
                result.write("-------------------------------\n")
                continue
            new_formula = synthesize_for_model(chosen_model)
            for model in models:
                if model == chosen_model and not evaluate(new_formula, model):
                    result.write('Fail\n')
                    continue
                elif model != chosen_model and evaluate(new_formula, model):
                    result.write('Fail\n')
                    continue
            result.write("-------------------------------\n")
            counter += 1


def task_7(formulas):
    with open('./results/task7_temp', 'w') as result:
        counter = 1
        old_target = sys.stdout
        sys.stdout = result
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            models = list(all_models(list(formula.variables())))
            result.write('(%d) Task_7 testing formula: %s Result: %s\n' % (counter, formula.infix(), truth_values(formula, models) == truth_values(synthesize(models, truth_values(formula, models)), models)))
            result.write("-------------------------------\n")
            counter += 1
        sys.__stdout__ = old_target


def run_tests():
    with open('./tests/hard_infix.text', 'r') as f_infix:
        formulas = f_infix.readlines()
        with open('./tests/task1_test') as task1_file:
            task_1(task1_file.readlines())
        task_2(formulas)
        task_3(formulas)
        task_4(formulas)
        task_5(formulas)
        task_6(formulas)
    with open('./tests/normal_infix.text') as f_infix:
        formulas = f_infix.readlines()
        task_7(formulas)

if __name__ == "__main__":
    run_tests()
