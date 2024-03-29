import time

""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/completeness.py """

from itertools import combinations as combinations
from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.prenex import *
from predicates.util import *
from predicates.deduction import *

permutations_by_k_dict = {}


def is_closed(sentences, constants):
    """ Return whether the given set of sentences closed with respect to the
        given set of constant names """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    return is_primitively_closed(sentences, constants) and \
           is_universally_closed(sentences, constants) and \
           is_existentially_closed(sentences, constants)


def create_all_combinations(temp_constants: set(), k: int) -> list():
    """
    help mehtod to return all permutations of constant, as list of Term objects
    """
    if k not in permutations_by_k_dict:
        list_of_subsets = list(product(temp_constants, repeat=k)) # create all subsets using product
        list_of_terms = []
        for temp_subset in list_of_subsets:
            subset_terms = []
            for var in temp_subset:
                subset_terms.append(Term(var)) # add Term(var) to subset
            list_of_terms.append(subset_terms)
        permutations_by_k_dict[k] = list_of_terms # add cur k to the dict holding all already made permutations
    return permutations_by_k_dict[k]


def is_primitively_closed(sentences: set(), constants: set()) -> bool:
    """ Return whether the given set of prenex-normal-form sentences is
        primitively closed with respect to the given set of constant names """
    relations_dict = {}
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
        if not is_quantifier(sentence.root): # we have something other then quantifier
            pair = sentence.relations() # get all relations
            while pair != set():
                relation_name, arity = pair.pop() #
                if relation_name not in relations_dict:
                    relations_dict[relation_name] = arity # add relation name and recived arity to mapping
    for constant in constants:
        assert is_constant(constant)

    for relation, arity in relations_dict.items():
        all_subsets_of_k = create_all_combinations(constants, arity) # get all constant permutation based on arity size
        for subset in all_subsets_of_k:
            cur_formula = Formula(relation, subset)
            cur_neg_formula = Formula('~', cur_formula)
            if cur_formula not in sentences and cur_neg_formula not in sentences:
                return False # neither of the normal formula form or it's negation does not appear in sentence
    return True

    # Task 12.1.1


def is_universally_closed(sentences, constants) -> bool:
    """ Return whether the given set of prenex-normal-form sentences is
        universally closed with respect to the given set of constant names """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)

    for sentence in sentences:
        if sentence.root == 'A':
            v = sentence.variable # cur variable
            r = sentence.predicate  # r is for inner formula
            for constant in constants:
                cur_sub = r.substitute({v: Term(constant)}) # for each constant, substitute with v
                if cur_sub not in sentences:
                    return False # we didnt found the sub in F , return false
    return True # all subs were found
    # Task 12.1.2


def is_existentially_closed(sentences, constants):
    """ Return whether the given set of prenex-normal-form sentences is
        existentially closed with respect to the given set of constant names """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    for sentence in sentences:
        if sentence.root == 'E':
            v = sentence.variable  # the var in the quntifier
            r = sentence.predicate  # r is for inner formula
            match = False
            for constant in constants:  # iter over all constants
                cur_sub = r.substitute({v: Term(constant)})
                if cur_sub in sentences:
                    match = True
                    break  # we found one match, break and then go to next sentence
            if not match:
                return False  # no matches were found, return false
    return True
    # Task 12.1.3


def find_unsatisfied_quantifier_free_sentence(sentences, constants, model,
                                              unsatisfied):
    def fuqfs_helper(unsatisfied):
        """
            helper func to remove on quantifier
            note that it does not matter if we have E or A.
                if we have A then sub is in sentences for sure, but may not 'not' satisfy M
                if we have E then sub does not satisfy M for sure, but may not be in sentences
        """
        for constant in constants:
            v = unsatisfied.variable  # the var in the quntifier
            inner_formula = unsatisfied.predicate  # the inner formula after the A
            substituted_formula = inner_formula.substitute({v: Term(constant)})
            # this sentence is in F and does not satisfy M:
            if substituted_formula in sentences and not model.evaluate_formula(substituted_formula):
                return substituted_formula
        return None

    """ Given a set of prenex-normal-form sentences that is closed with respect
        to the given set of constants names, given a model whose universe is
        the given set of constant names, and given a sentence (which possibly
        contains quantifiers) from the given set that the given model does not
        satisfy, return a quantifier-free sentence from the given set that the
        given model does not satisfy. The set sentences may only be accessed
        using containment queries, i.e., using the "in" operator as in:
        if sentence in sentences """
    for constant in constants:
        assert is_constant(constant)
    assert type(model) is Model
    assert model.universe == constants
    assert type(unsatisfied) is Formula
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)

    while unsatisfied.root is 'A' or unsatisfied.root is 'E':  # remove one quantifier at every iteration
        unsatisfied = fuqfs_helper(unsatisfied)
        assert unsatisfied  # if unsatisfied is None then something went wrong
    return unsatisfied  # we have a unsatisfied formula without any quantifiers

    # Task 12.2


def get_primitives(quantifier_free):
    def get_prime_helper(q_f, ret):
        """
        :param q_f: the quantifier_free formula to get prime formula of
        :param ret: the over all set used to save the prime formula'
        """
        if is_relation(q_f.root):
            ret.add(q_f)
        elif is_binary(q_f.root):
            get_prime_helper(q_f.first, ret)
            get_prime_helper(q_f.second, ret)
        elif is_unary(q_f.root):
            get_prime_helper(q_f.first, ret)

    """ Return a set containing the primitive formulae (i.e., relation
        instantiations) that appear in the given quantifier-free formula. For
        example, if quantifier_free is '(R(c1,d)|~(Q(c1)->~R(c2,a))', then the
        returned set should be {'R(c1,d)', 'Q(c1)', 'R(c2,a)'} """
    assert type(quantifier_free) is Formula and \
           is_quantifier_free(quantifier_free)
    ret = set()
    get_prime_helper(quantifier_free, ret)
    return ret

    # Task 12.3.1


def model_or_inconsistent(sentences, constants):
    def get_H(prime_set) -> list():
        """
        H is the group of prime formula derived from G - a quantifier-free sentence prime forumla or thier negation
        that exsists in F
        :return: H
        """
        H = []
        for prime in prime_set:
            str_prime = str(prime)
            if prime in sentences:
                H.append(str_prime)
            if Formula('~', prime) in sentences:
                H.append('~' + str_prime)
        return H

    """ Given a set of prenex-normal-form sentences that is closed with respect
        to the given set of constants names, return either a model for the
        given set of sentences, or a proof of a contradiction from these
        sentences as assumptions """

    assert is_closed(sentences, constants)
    primitives_list = []
    for sentence in sentences:
        # check that the sentence is a relation quantifier
        if is_relation(sentence.root):
            # update the list with the relation and the variables inside
            primitives_list.append(sentence)
    # what we need to do is to create a dictionary where the relation name is the key and there is a set in the
    # value. the set will contain all the written permutations of the constants in the relation.
    # so now we will run on the primitives_list, and if the relation name doesn't appear in the dictionary,
    # we shall add it and add the relations as a tuple to the set
    model_meaning = {}
    model_is_true = True
    # add all constants to the model_meaning as their own values
    for constant in constants:
        model_meaning[constant] = constant
    # for each primitive value, we will want to run on all the relation's arguments and them as a tuple to the
    # meaning of the relation.
    for prim in primitives_list:
        constants_list = []
        # create a constants_list of all arguments
        for arg in prim.arguments:
            constants_list.append(arg.root)
        # if the relation doesn't exists in the meaning_model, add it
        if prim.root not in model_meaning:
            model_meaning[prim.root] = {tuple(constants_list)}
        # else, add the constants_list as a tuple
        else:
            model_meaning[prim.root].add(tuple(constants_list))
    # create the new model
    new_model = Model(constants, model_meaning)
    false_sentence = None
    # check for each sentence in the sentences if the sentence evaluates with the model
    # ( actually we want to know if the formula satisfies the model)
    for sentence in sentences:
        false_sentence = sentence
        if not new_model.evaluate_formula(sentence):
            model_is_true = False  # raise the flag if we stopped the evaluation mid-run
            break
    # if we didn't stop the run, then the model is good. return it.
    if model_is_true:
        return new_model
    # run task 2 on the given false sentence
    phi = find_unsatisfied_quantifier_free_sentence(sentences, constants, new_model,
                                                    false_sentence)
    assert false_sentence  # check that it's not None
    primitive_formulae = get_primitives(phi)  # get set G
    assumptions = get_H(primitive_formulae)  # get set H from G
    assumptions.append(str(phi))  # add phi to assumptions
    not_phi = Formula('~', phi)
    not_phi_str = str(not_phi)
    contradiction = str(Formula('&', phi, not_phi))  # this is the contradiction we wish to prove
    new_prover = Prover(assumptions, contradiction)
    line_number_dict = {}

    # --START OF PROOF--
    for assumption in assumptions:  # adding all assumptions -> H and phi
        cur_step = new_prover.add_assumption(assumption)
        line_number_dict[assumption] = cur_step
    step_get_not_phi = new_prover.add_tautological_inference(not_phi_str,
                                                             list(line_number_dict.values()))  # get not_phi
    line_number_dict[not_phi] = step_get_not_phi
    step_final = new_prover.add_tautological_inference(contradiction,
                                                       [line_number_dict[phi], line_number_dict[not_phi]])
    return new_prover.proof
    # Task 12.3.2


def combine_contradictions(proof_true, proof_false):
    """ Given two proofs of contradictions from two lists of assumptions that
        differ only in the last assumption, where the last assumption of
        proof_false is the negation of that of proof_true, return a proof of a
        contradiction from only the assupmtions common to both proofs (without
        the last assumption of each proof). You can assume that each of the
        given proofs has Prover.AXIOMS (in order) as its first six
        axioms/assumptions, and that all of its axioms/assumptions are
        sentences """
    assert type(proof_true) is Proof and type(proof_false) is Proof
    assert proof_true.assumptions[:-1] == proof_false.assumptions[:-1]
    assert proof_false.assumptions[-1].templates == set()
    assert proof_true.assumptions[-1].templates == set()
    assert proof_false.assumptions[-1].formula == \
           Formula('~', proof_true.assumptions[-1].formula)
    # Task 12.4
    # get the last assumptions from the assumptions list of the two proofs
    last_assumption_true = str(proof_true.assumptions[-1].formula)
    last_assumption_false = str(proof_false.assumptions[-1].formula)

    # create two new proofs out of the true/false proofs, where each conclusion is the negation of the last
    # assumption of the proof
    proof_by_contradiction_true = proof_by_contradiction(proof_true, last_assumption_true)
    proof_by_contradiction_false = proof_by_contradiction(proof_false, last_assumption_false)

    # this is the contradiction we wish to prove, from the two conclusions of the above proofs
    true_proof_conclusion = proof_by_contradiction_true.conclusion
    false_proof_conclusion = proof_by_contradiction_false.conclusion
    contradiction = str(Formula('&', true_proof_conclusion, false_proof_conclusion))

    # create a new proof out of the first assumptions, and the conclusion is a contradiction based from AND between
    # the two former conclusions
    # --START PROOF--
    new_prover = Prover(proof_by_contradiction_true.assumptions, contradiction)

    # we now add the whole proofs to the new proof, and save the line number of each conclusion
    true_conclusion_line_number = new_prover.add_proof(true_proof_conclusion, proof_by_contradiction_true)
    false_conclusion_line_number = new_prover.add_proof(false_proof_conclusion, proof_by_contradiction_false)
    # last of all, we use the tautological inference rule to return a line where we conclude the stated conclusion,
    # and return the proof
    final_line = new_prover.add_tautological_inference(contradiction,
                                                       [true_conclusion_line_number, false_conclusion_line_number])
    return new_prover.proof


def eliminate_universal_instance_assumption(proof, constant):
    """ Given a proof of a contradiction from a list of assumptions, where the
        last assumption is an instantiation of the form 'formula(consatnt)'
        (for the given constant name) of the universal assumption of the form
        'Ax[formula(x)]' that immediately precedes it, return a proof of a
        contradiction from the same assumptions without the last (universally
        instantiated) one. You can assume that the given proof has
        Prover.AXIOMS (in order) as its first six axioms/assumptions, and that
        all of its axioms/assumptions are sentences """
    assert type(proof) is Proof
    assert proof.assumptions[-2].templates == set()
    assert proof.assumptions[-1].templates == set()
    assert proof.assumptions[-2].formula.root == "A"
    assert proof.assumptions[-1].formula == \
           proof.assumptions[-2].formula.predicate.substitute(
               {proof.assumptions[-2].formula.variable: Term(constant)})

    # Task 12.5

    last_assumption = proof.assumptions[-1].formula

    # return a contradiction proof of the given proof
    new_proof_by_contradiction = proof_by_contradiction(proof, str(last_assumption))

    # create a new proof
    # --START PROOF--
    new_prover = Prover(proof.assumptions[:-1], proof.conclusion)

    # add whole proof of the contradiction proof we've just created
    contradiction_proof_line_number = new_prover.add_proof(new_proof_by_contradiction.conclusion,
                                                           new_proof_by_contradiction)

    # create line using UI axiom, with the following map
    #  we takes the last assumption of the NEW list of assumptions - that means 'Ax[R(x)]'
    quantified_form = new_prover.proof.assumptions[-1].formula
    ui_instantiation_map = {'R(' + quantified_form.variable + ')': str(quantified_form.predicate),
                            'x': quantified_form.variable,
                            'c': constant}
    quantified_assumption_line_number = new_prover.add_assumption(str(quantified_form))
    ui_line_number = new_prover.add_instantiated_assumption(
        str(Formula('->', new_prover.proof.assumptions[-1].formula, last_assumption)), Prover.UI, ui_instantiation_map)

    # add tautological line that involves the UI line and the last line of the quantified assumption, to create the
    #  contradiction assumption
    tautological_line_number = new_prover.add_tautological_inference(
        str(last_assumption), [ui_line_number, quantified_assumption_line_number])

    # add tautological line that involves the conclusion from the contradiction proof and the last line, so together
    # we create again the contradiction from the original proof
    conclusion_line_number = new_prover.add_tautological_inference(str(proof.conclusion),
                                                                   [contradiction_proof_line_number,
                                                                    tautological_line_number])
    return new_prover.proof


def universally_close(sentences: set(), constants: set()) -> set():
    """ Return a set of sentences that contains the given set of
        prenex-normal-form sentences and is universally closed with respect to
        the given set of constant names. For example, if sentences is the
        singleton {'Ax[Ay[R(x,y)]]'} and constants is {a,b}, then the returned
        set should be: {'Ax[Ay[R(x,y)]]', 'Ay[R(a,y)]', 'Ay[R(b,y)]', 'R(a,a)',
        'R(a,b)', 'R(b,a)', 'R(b,b)'} """
    global permutations_by_k_dict
    permutations_by_k_dict = {}

    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    # Task 12.6
    added_sentences = set()  # the set of added sentences
    for sentence in sentences:
        k = 0
        substitution_set = []  # this is our set of already added var's , in prev scopes
        while sentence.root == 'A':
            k += 1  # we added a var
            # create all the products in size k, use dict of already made products to cut run time
            constants_product = create_all_combinations(constants, k)
            var = sentence.variable  # the cur var
            if var not in substitution_set:
                substitution_set.append(var)  # add that var if it's not already added
            sentence = sentence.predicate  # we are now looking at the inner predicate
            substitution_map = {}
            for constant_in_size_k in constants_product:  # iterate over all made products
                for cur_constant, added_var in zip(constant_in_size_k, substitution_set):
                    substitution_map[added_var] = cur_constant  # connect each var to a constant
                temp_sentence = sentence.substitute(substitution_map)  # make sub to the sentences
                if temp_sentence not in added_sentences:
                    added_sentences.add(temp_sentence)  # add that sentence
    return added_sentences.union(sentences)


def replace_constant(proof, constant, variable='zz'):
    """ Given a proof, a constant name that (potentially) appears in the
        assumptions and/or proof, and a variable name that does not appear
        anywhere in the proof or assumptions, return a "similar" (and also
        valid) proof where every occurrence of the given constant name in the
        assumptions and proof is replaced with the given variable name. You may
        assume that the given constant name only appears in the assumption
        schemata of the given proof as a non-template constant name """
    assert is_constant(constant)
    assert is_variable(variable)
    assert type(proof) is Proof
    proof_new_assumptions = []
    substitude_dict = {constant: Term(variable)}
    for assumption in proof.assumptions: # sub constant with var for each assumption
        new_schema = Schema(str(assumption.formula.substitute(substitude_dict)), assumption.templates)
        proof_new_assumptions.append(new_schema)
    proof_new_conclusion = proof.conclusion.substitute(substitude_dict) # sub conclusion with var
    new_prover = Prover(proof_new_assumptions, proof_new_conclusion) # create new_prover
    for line in proof.lines:
        new_line_formula = line.formula.substitute(substitude_dict) # change cur line with mapping
        if line.justification[0] == 'A': #
            new_instantiation_map = {}
            for key, value in line.justification[2].items():
                if is_relation(key[0]): # we have a relation, use Formual's parse and sub with mapping
                    new_instantiation_map[key] = str(Formula.parse(value).substitute(substitude_dict))
                else: # we have a term, use Term's parse and sub with mapping
                    new_instantiation_map[key] = str(Term.parse(value).substitute(substitude_dict))
            # add the needed prev justifications as well as created mapping
            new_line_justification = (line.justification[0], line.justification[1], new_instantiation_map)
        else:
            new_line_justification = line.justification # just take the original line justifications
        new_prover._add_line(new_line_formula, new_line_justification) # add line to new prover
    return new_prover.proof
    # Task 12.7


def eliminate_existential_witness_assumption(proof, constant):
    """ Given a proof of a contradiction from a list of assumptions, where the
        last assumption is a witness of the form 'formula(constant)' (for the
        given constant name) for the existential assumption of the form
        'Ex[formula(x)]' that immediately precedes it, and where the given
        constant name does not appear anywhere else in the assumptions, return
        a proof of a contradiction from the same assumptions without the last
        (witness) one. You can assume that the given proof has Prover.AXIOMS
        (in order) as its first six axioms/assumptions, and that all of its
        axioms/assumptions are sentences """
    assert type(proof) is Proof
    assert proof.assumptions[-2].templates == set()
    assert proof.assumptions[-1].templates == set()
    assert proof.assumptions[-2].formula.root == "E"
    assert proof.assumptions[-1].formula == \
           proof.assumptions[-2].formula.predicate.substitute(
               {proof.assumptions[-2].formula.variable: Term(constant)})

    # replace the constant with a 'zz' variable in the given proof
    proof_replaced_consant = replace_constant(proof, constant)

    # save the last formula form assumption from the original proof ( where the assumption will be 'phi(zz)'
    last_origin_assumption = proof_replaced_consant.assumptions[-1].formula

    # create a new proof by contradiction that will no longer hold phi(zz) as the assumption, and the conclusion of
    # the proof will be '~phi(zz)'
    new_proof_by_contradiction = proof_by_contradiction(proof_replaced_consant, str(last_origin_assumption))

    # save the last formula form assumption of the new contradicted proof (that will be 'Ex[phi(x)]'
    last_new_assumption = new_proof_by_contradiction.assumptions[-1].formula

    # create the new conclusion for the returned proof - '(Ex[phi(x)]&~Ex[phi(x)])'
    new_conclusion = Formula('&', last_new_assumption, Formula('~', last_new_assumption))

    # create new proof by the assumption of the contradicted proof and the new conclusion
    new_prover = Prover(new_proof_by_contradiction.assumptions, new_conclusion)

    # add the contradicted proof to the lines of the new proof ('~phi(zz)')
    proof_line = new_prover.add_proof(new_proof_by_contradiction.conclusion, new_proof_by_contradiction)

    # crete formula for '~phi(zz)'
    # negate_last_origin_assumption = Formula('~', last_origin_assumption)
    existance_assumption_var = last_new_assumption.variable

    # create back ~phi(x)
    free_instantiated_assumption = new_proof_by_contradiction.conclusion.substitute({'zz': Term(existance_assumption_var)})

    # added the line to create '~phi(x)' back
    free_instantiated_step = new_prover.add_free_instantiation(free_instantiated_assumption, proof_line,
                                                               {'zz': existance_assumption_var})

    # create formula for '(~phi(x)->(phi(x)->~Ex[phi(x)]))
    tautology_formula = Formula('->', free_instantiated_assumption.first, Formula('~', last_new_assumption))
    # add the tautology line of the above formula
    # tautology_line = new_prover.add_tautology(tautology_formula)

    # add the tautological inference of the formula '(phi(zz)->~Ex[phi(x)])'
    second_EI_step = new_prover.add_tautological_inference(str(tautology_formula), [free_instantiated_step])

    # add the assumption of the last assumption 'Ex[phi(x)]'
    first_EI_step = new_prover.add_assumption(str(last_new_assumption))

    penultimate_step = new_prover.add_existential_derivation( str(Formula('~', last_new_assumption)),
                                                              first_EI_step,second_EI_step)
    final_step = new_prover.add_tautological_inference(str(new_conclusion),[first_EI_step,penultimate_step])
    return new_prover.proof
    # Task 12.8


def existentially_close(sentences, constants):

    def add_inner(sentence , var, map):
        """
        the sentence received had a E quantifier, create a fresh constant and insert it instead of received var
        and update calling function sets
        :param sentence: sentence with prev E quantifier
        :param var: the variable to switch
        :param map: a prev mapping used in this sentence upper scopes
        """
        cur_c = next(fresh_constant_name_generator) # create new constant
        new_contansts.add(cur_c) # add the constant to upper scope set
        map[var] = Term(cur_c) # add var to mapping
        new_sentences.add(sentence.substitute(map)) # sub sentence with cur mapping
        if sentence.root == 'E':
            add_inner(sentence.predicate, sentence.variable, map) # we met another E quantifier, call add_inner

    """ Return a pair of a set of sentences that contains the given set of
        prenex-normal-form sentences and a set of constant names that contains
        the given set of constant names, such that the returned set of
        sentences is universally closed with respect to the returned set of
        constants names. For example, if sentences is the singleton
        {'Ex[Ey[R(x,y)]]'} and constants is {a,b}, then the returned set could
        be: {'Ex[Ey[R(x,y)]]', 'Ey[R(c1,y)]', 'R(c1,c2)'}. New constant names
        should be generated using next(fresh_constant_name_generator) """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
        # Task 12.9
        new_sentences = set() # create set for sentences
        new_contansts = set().union(constants) # create set for constants
        for sentence in sentences:
            new_sentences.add(sentence) # add cur sentence
            if sentence.root == 'E':
                add_inner(sentence.predicate, sentence.variable, {}) # deal with inner predicate

        return (new_sentences, new_contansts)
