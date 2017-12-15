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

    def appeand_to_sequence(cu_formula, helper_sequence):
        """

        :param cu_formula:
        :param helper_sequence:
        :return:
        """
        if is_function(cu_formula.root):
            term_list = compile_term(cu_formula)
            helper_sequence = helper_sequence + term_list

            term_list = helper_sequence[-1].first
            return term_list, helper_sequence
        else:
            return cu_formula, helper_sequence

    def handle_relation(steps_list, final_formula):
        """
        make every function that comes to be a relation, implie it to the next relations by recursion, and quantify it.
        we enter to this function only when we handle relations and equations.
        :param steps_list:  list of formulas
        :param final_formula:  the final formula that we will put all together
        :return:
        """
        if len(steps_list) == 0:
            return final_formula
        term = steps_list[0]
        relation = make_func_to_relation(term.second, term.first)
        formula_before_quantified = Formula('->', relation, handle_relation(steps_list[1:], final_formula))
        return Formula('A', term.first.root, formula_before_quantified)

    def rfwrif_helper(temp_formula: Formula):
        """
        main method for the function. we seperate our cases by each type of formula, and handle each type differently.
        :param temp_formula: current formula that we modify
        :return:
        """
        steps_list = []
        if is_relation(temp_formula.root):
            new_relation_args = []  # create new list for new arguments of the relations
            for arg in temp_formula.arguments:
                # if the root is form of a function, we will go on recursion on it with compile_term
                term, steps_list = appeand_to_sequence(arg, steps_list)

                new_relation_args.append(term)  # R(f(g(h(x))),y,3) = > R(z3,y,3)
            return handle_relation(steps_list, Formula(temp_formula.root, new_relation_args))

        elif is_equality(temp_formula.root):  # Populate self.first and self.second # b=f(a)
            term_first, steps_list = appeand_to_sequence(temp_formula.first, steps_list)  # b
            term_second, steps_list = appeand_to_sequence(temp_formula.second, steps_list)  # f(a) = z1
            return handle_relation(steps_list, Formula(temp_formula.root, term_first, term_second))

        elif is_quantifier(temp_formula.root):  # Populate self.variable and self.predicate

            inner_forula = rfwrif_helper(temp_formula.predicate)
            return Formula(temp_formula.root, temp_formula.variable, inner_forula)

        elif is_unary(temp_formula.root):  # Populate self.first
            step_formula = rfwrif_helper(temp_formula.first)

            return Formula(formula.root, step_formula)

        else:
            first_step = rfwrif_helper(temp_formula.first)
            second_step = rfwrif_helper(temp_formula.second)
            return Formula(temp_formula.root, first_step, second_step)

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
    return list_of_sequences


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

    def rfwrif_helper(form: Formula):
        function_list = form.functions()
        form = replace_functions_with_relations_in_formula(form)
        returned_list.append(str(form))
        # relation_list = (form.relations())
        # run on all relations in the form, and for each - create a new form - to check each relation
        for (func, arity) in function_list:
            first_part = ''
            second_part = ''
            arity_list = []
            arity += 1
            func = func[0].upper() + func[1:]

            # first part
            for i in range(1, arity):
                first_part += 'Ax' + str(i) + '['  # open quantify for each variable in relation
                arity_list.append('x' + str(i))

            first_part += 'Ez[' + func + '(z'  # open quantify for specific z and open relation
            while arity_list != []:
                first_part += ',' + arity_list.pop(0)  # add x1,x2,etc..
            first_part += ')]'  # close relation and EZ
            for i in range(arity - 1):
                first_part += ']'  # close Axs

            # second part
            for i in range(1, arity):
                second_part += 'Ax' + str(i) + '['  # open quantify for each variable in relation (Ax1,Ax2...)
                arity_list.append('x' + str(i))  # 2 times '['
            # open Az1, Az2 and relation, open & and open ->, and start relation
            second_part += 'Az1[Az2[((' + func + '(z1'  # ([([(((
            for i in range(arity - 1):
                second_part += ',' + arity_list[i]  # add x1,x2,etc.. to relation
            second_part += ')&' + func + '(z2'  # ) &( close relation, and close &, and open another relation
            while arity_list != []:
                second_part += ',' + arity_list.pop(0)  # add x1,x2,etc.. to relation

            # close relation, close ->, close Az1 close Az2
            second_part += '))->z1=z2)]]'  # )) -> )])])
            for i in range(arity - 1):
                second_part += ']'  # 2 times ] # close Axs...
            returned_list.append('(' + first_part + '&' + second_part + ')')  # ( & )
            # print(second_part)

    for formula in formulae:
        assert type(formula) is str
        # task 8.6
    returned_list = []
    for formula in formulae:
        rfwrif_helper(Formula.parse(formula))
    return returned_list


def replace_equality_with_SAME(formulae):

    def helper_same(help_formula: Formula):
        if is_relation(help_formula.root):  # Populate self.root and self.arguments
            return Formula(help_formula.root,help_formula.arguments)
        elif is_equality(help_formula.root):  # Populate self.first and self.second
            first = help_formula.first
            second = help_formula.second
            return Formula('SAME',[first,second])
        elif is_quantifier(help_formula.root): # Populate self.variable and self.predicate
            return Formula(help_formula.root,help_formula.variable, helper_same(help_formula.predicate))
        elif is_unary(help_formula.root): # Populate self.first
            return Formula(help_formula.root,helper_same(help_formula.first))
        else: # Populate self.first and self.second
            return Formula(help_formula.root,helper_same(help_formula.first),helper_same(help_formula.second))

    def get_rules_for_same(ret,formula):
        relation_list = formula.relations()
        ret.append('SAME(x,x)')
        ret.append('(SAME(x,y)->SAME(y,x))')
        ret.append('((SAME(x,y)&SAME(y,z))->SAME(x,z))')
        for relation, arity in relation_list:
            relation_same_formula = ''
            for i in range(1,arity+1):
                relation_same_formula += 'Ax'+str(i)+'['
                relation_same_formula += 'Ay'+str(i)+'['

            relation_same_formula+= '(' + '(' * (arity-1) # open for IMPLICATION and open for & * # of times of x1...

            for i in range(1, arity + 1):
                if i != 1:
                    relation_same_formula += '&'
                relation_same_formula += 'SAME(x'+str(i)+',y'+str(i)+')'
                if i != 1:
                    relation_same_formula += ')' # close the openings for &
            relation_same_formula +='->('+relation+'('
            for i in range(1,arity+1):
                if i != 1:
                    relation_same_formula += ','
                relation_same_formula+= 'x'+str(i)
            relation_same_formula+=')->'+relation+'('
            for i in range(1, arity + 1):
                if i != 1:
                    relation_same_formula += ','
                relation_same_formula += 'y' + str(i)
            relation_same_formula+= ')))'
            relation_same_formula += ']' * 2*arity
            ret.append(relation_same_formula)

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
        ret = []
        for formula in formulae:
            formula = Formula.parse(formula)
            ret.append(str(helper_same(formula)))
            get_rules_for_same(ret,formula)
        return ret
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
