""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/deduction.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *


def make_implication(assumption, line_formula):
    return '(' + str(assumption) + '->' + str(line_formula) + ')'


def inverse_mp(proof, assumption, print_as_proof_forms=False):
    def make_tautology(first, second):
        return '(' + str(first) + '->(' + str(second) + '->' + str(first) + ')' + ')'

    """ Takes a proof, whose first six assumptions/axioms are Prover.AXIOMS, of
        a conclusion from a list of assumptions/axioms that contains the given
        assumption as a simple formula (i.e., without any templates), where no
        step of the proof is a UG step over a variable that is free in the
        given assumption, and returns a proof of (assumption−>conclusion) from
        the same assumptions except assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is str
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions[:len(Prover.AXIOMS)] == Prover.AXIOMS
    # Task 11.1

    # create new assumptions
    new_proof_assump = copy.deepcopy(proof.assumptions)
    del new_proof_assump[(new_proof_assump.index(Schema(assumption)))]

    # create new conclusion
    new_conclusion = make_implication(assumption, proof.conclusion)
    # new_proof = Proof(new_proof_assump, new_conclusion, [])
    new_prover = Prover(new_proof_assump, new_conclusion, print_as_proof_forms)

    line_num_conc_dict = {}
    # divide to cases and run recurs
    for line in proof.lines:
        l_type = line.justification[0]
        l_formula = line.formula
        if l_type == 'A':
            if l_formula == assumption:
                conc = make_tautology(assumption, assumption)
                step_1 = new_prover.add_tautology(conc)
                line_num_conc_dict[conc] = step_1

            else:
                step_1 = new_prover.add_tautology(make_tautology(l_formula, assumption))  # T -> assumption -> T
                step_2 = new_prover.add_instantiated_assumption(l_formula, proof.assumptions[line.justification[1]],
                                                                line.justification[2])
                conc = make_implication(assumption, l_formula)  # we want assumption -> T
                step_3 = new_prover.add_mp(conc, step_2, step_1)  # do MP and we get assumption -> T
                line_num_conc_dict[conc] = step_3
        elif l_type == 'T':
            step_1 = new_prover.add_tautology(make_tautology(l_formula, assumption))  # T -> assumption -> T
            step_2 = new_prover.add_tautology(l_formula)
            conc = make_implication(assumption, l_formula)  # we want assumption -> T
            step_3 = new_prover.add_mp(conc, step_2, step_1)  # do MP and we get assumption -> T
            line_num_conc_dict[conc] = step_3

        elif l_type == 'MP':
            psi_1 = proof.lines[line.justification[1]].formula
            if psi_1 == assumption:
                new_psi_1 = line_num_conc_dict[make_tautology(assumption, psi_1)]
            else:
                new_psi_1 = line_num_conc_dict[make_implication(assumption, psi_1)]
            psi_2 = proof.lines[line.justification[2]].formula
            new_psi_2 = line_num_conc_dict[make_implication(assumption, psi_2)]
            # assert (new_psi_1, new_psi_2)  # check that we found the looked up psi1 and psi2
            conc = make_implication(assumption, l_formula)
            step_1 = new_prover.add_tautological_inference(conc, [new_psi_2, new_psi_1])
            line_num_conc_dict[conc] = step_1
            # (plus(minus(a),plus(a,c))=plus(minus(a),plus(a,c))->((plus(a,c)=a->(plus(minus(a),plus(a,c))=plus(minus(a),plus(a,c))->plus(minus(a),plus(a,c))=plus(minus(a),a)))->plus(minus(a),plus(a,c))=plus(minus(a),a)))
        elif l_type == 'UG':
            var = str(l_formula.variable)
            l_just = proof.lines[line.justification[1]].formula
            ug_base_formula = make_implication(assumption, l_just)  # we have assumption -> cur somewhere
            ug_base_formula_line_number = line_num_conc_dict[ug_base_formula]
            ug_formula = 'A' + var + '[' + ug_base_formula + ']'  # Ax[Q()->R(x)]
            step_1 = new_prover.add_ug(ug_formula, ug_base_formula_line_number)  # Ax[assumption -> R(x)]

            instantiation_map = {'x': var, 'Q()': str(assumption), 'R(' + var + ')': str(l_formula.predicate)}
            us_formula = new_prover.US.instantiate(instantiation_map)
            step_2 = new_prover.add_instantiated_assumption(us_formula, new_prover.US, instantiation_map)
            # the us_formula.second suppose to be __ but instead it's (plus(a,c)=a->Ax[Ax[(plus(a,c)=a->plus(plus(x,y),z)=plus(x,plus(y,z)))]])
            step_3 = new_prover.add_tautological_inference(str(us_formula.second), [step_1, step_2])
            line_num_conc_dict[us_formula.second] = step_3

    return new_prover.proof


def proof_by_contradiction(proof: Proof, assumption: str, print_as_proof_forms=False):
    """ Takes a proof, whose first six assumptions/axioms are Prover.AXIOMS, of
        a contradiction (a formula whose negation is a tautology)  a list of
        assumptions/axioms that contains the given assumption as a simple
        formula (i.e., without any templates), where no step of the proof is a
        UG step over a variable that is free in the given assumption, and
        returns a proof of ~assumption from the same assumptions except
        assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is str
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions[:len(Prover.AXIOMS)] == Prover.AXIOMS
    # Task 11.2
    # create negate to assumption == conclusion for our proof
    new_conclustion = '~' + assumption

    # create a copy for the original assumptions and delete the assumption we received as input
    new_assumption = copy.deepcopy(proof.assumptions)
    del new_assumption[(new_assumption.index(Schema(assumption)))]

    # create new Prover object
    new_prover = Prover(new_assumption, new_conclustion, print_as_proof_forms)

    # add the proof of inverse_mp without the input assumption
    proofs_conclustion = new_prover.add_proof(make_implication(assumption, proof.conclusion),
                                              inverse_mp(proof, assumption, print_as_proof_forms))
    # add tautology that looks like '((assumption->conclusion)->~assumption)'
    tautology_line_number = new_prover.add_tautology(make_implication(new_prover.proof.lines[
                                                                         proofs_conclustion].formula, new_conclustion))
    # do MP on the last two lines and receive our conclusion.
    new_prover.add_tautological_inference(new_conclustion,[tautology_line_number,proofs_conclustion])
    return new_prover.proof
