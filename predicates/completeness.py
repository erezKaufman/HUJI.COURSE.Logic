""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/completeness.py """

from itertools import  combinations as combinations
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
            cur_formula =Formula(relation,subset)
            cur_neg_formula = Formula('~',cur_formula)
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
            r = sentence.predicate # r is for inner formula
            for constant in constants:
                cur_sub = r.substitute({v:Term(constant)})
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
            inner = unsatisfied.predicate # the inner formula after the A
            sub = inner.substitute({v: Term(constant)})
            if sub in sentences and not model.evaluate_formula(sub): # this sentence is in F and does not satisfy M:
                return sub
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

    while(unsatisfied.root is 'A' or unsatisfied.root is 'E'): # remove one quantifier at every iteration
        unsatisfied = fuqfs_helper(unsatisfied)
        assert unsatisfied # if unsatisfied is None then something went wrong
    return unsatisfied # we have a unsatisfied formula without any quantifiers

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
            get_prime_helper(q_f.first,ret)
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
    """ Given a set of prenex-normal-form sentences that is closed with respect
        to the given set of constants names, return either a model for the
        given set of sentences, or a proof of a contradiction from these
        sentences as assumptions """
    assert is_closed(sentences, constants)
    # for sentence in sentences
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
               {proof.assumptions[-2].formula.variable:Term(constant)})
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
               {proof.assumptions[-2].formula.variable:Term(constant)})
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

# if __name__ == '__main__':
#     f = Formula.parse('(R(c1,d)|~(Q(c1)->~R(c2,a)))')
#     s = get_primitives(f)
#     print(s)