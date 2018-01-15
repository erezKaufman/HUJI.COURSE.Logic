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


def is_primitively_closed(sentences: set(), constants: set()):
    def create_all_combinations(constants: set(), k: int):
        """
        help mehtod to return all permutations of constant, as list of Term objects
        """
        if k not in permutations_by_k_dict:
            list_of_subsets = list(product(constants, repeat=k))
            list_of_terms = []
            for subset in list_of_subsets:
                subset_terms = []
                for var in subset:
                    subset_terms.append(Term(var))
                list_of_terms.append(subset_terms)
            permutations_by_k_dict[k] = list_of_terms
        return permutations_by_k_dict[k]

    """ Return whether the given set of prenex-normal-form sentences is
        primitively closed with respect to the given set of constant names """
    relations_dict = {}
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
        if not is_quantifier(sentence.root):
            pair = sentence.relations()
            while pair != set():
                relation_name, arity = pair.pop()
                if relation_name not in relations_dict:
                    relations_dict[relation_name] = arity
    for constant in constants:
        assert is_constant(constant)

    for relation, arity in relations_dict.items():
        all_subsets_of_k = create_all_combinations(constants, arity)
        for subset in all_subsets_of_k:
            cur_formula = Formula(relation, subset)
            cur_neg_formula = Formula('~', cur_formula)
            if cur_formula not in sentences and cur_neg_formula not in sentences:
                return False
    return True

    # Task 12.1.1


def is_universally_closed(sentences, constants):
    """ Return whether the given set of prenex-normal-form sentences is
        universally closed with respect to the given set of constant names """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)

    for sentence in sentences:
        if sentence.root == 'A':
            v = sentence.variable
            r = sentence.predicate  # r is for inner formula
            for constant in constants:
                cur_sub = r.substitute({v: Term(constant)})
                if cur_sub not in sentences:
                    return False
    return True
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

    while (unsatisfied.root is 'A' or unsatisfied.root is 'E'):  # remove one quantifier at every iteration
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
            # str_prime = str(prime)
            if prime in sentences:
                H.append(prime)
            if Formula('~', prime) in sentences:
                H.append(Formula('~', prime))
            if is_unary(prime.root) and prime.first in sentences:
                H.append(prime.first)
        return H

    """ Given a set of prenex-normal-form sentences that is closed with respect
        to the given set of constants names, return either a model for the
        given set of sentences, or a proof of a contradiction from these
        sentences as assumptions """

    assert is_closed(sentences, constants)
    primitives_list = []
    for sentence in sentences:
        # check that the sentence is not quantifier
        if is_relation(sentence.root):
            # update the list with the relation and the variables inside
            primitives_list.append(sentence)
    # what we need to do is to create a dictionary where the relation name is the key and there is a set in the
    # value. the set will contain all the written permutations of the constants in the relation.
    # so now we will run on the primitives_list, and if the relation name doesn't appear in the dictionary,
    # we shall add it and add the relations as a tuple to the set
    model_meaning = {}
    model_is_true = True
    for constant in constants:
        model_meaning[constant] = constant
    for prim in primitives_list:
        constants_list = []
        for arg in prim.arguments:
            constants_list.append(arg.root)
        if prim.root not in model_meaning:
            model_meaning[prim.root] = {tuple(constants_list)}
        else:
            model_meaning[prim.root].add(tuple(constants_list))
            # print(prim.free_variables())
    new_model = Model(constants, model_meaning)
    for sentence in sentences:
        # print(sentence)
        false_sentence = sentence
        if not new_model.evaluate_formula(sentence):
            print(false_sentence)
            model_is_true = False
            break
    if model_is_true:
        return new_model
    # run task 2 on the given false sentence
    false_sentence = find_unsatisfied_quantifier_free_sentence(sentences, constants, new_model,
                                                               false_sentence)
    # test
    primitive_formulae = get_primitives(false_sentence)
    assumptions = get_H(primitive_formulae)
    assumptions.append(false_sentence)
    print(assumptions)
    conclusion = Formula('~', false_sentence)
    new_prover = Prover(assumptions, conclusion)
    line_number_dict = {}

    # --START OF PROOF--
    for assumption in assumptions:
        line_number_dict[assumption] = new_prover.add_assumption(assumption)



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


def universally_close(sentences, constants):
    """ Return a set of sentences that contains the given set of
        prenex-normal-form sentences and is universally closed with respect to
        the given set of constant names. For example, if sentences is the
        singleton {'Ax[Ay[R(x,y)]]'} and constants is {a,b}, then the returned
        set should be: {'Ax[Ay[R(x,y)]]', 'Ay[R(a,y)]', 'Ay[R(b,y)]', 'R(a,a)',
        'R(a,b)', 'R(b,a)', 'R(b,b)'} """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
        # Task 12.6


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
    # Task 12.8


def existentially_close(sentences, constants):
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
