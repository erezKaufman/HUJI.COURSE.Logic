""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/deduction.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *


def inverse_mp(proof, assumption, print_as_proof_forms=False):
    def make_tautology(first, second):
        return '('+str(first) + '->(' +str(second) + '->' + str(first)+')'+')'

    def make_implication(assumption, line):
        return '('+str(assumption) + '->' + str(line) +')'
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

    # create new assumptions
    new_proof_assump = copy.deepcopy(proof.assumptions)
    del new_proof_assump[(new_proof_assump.index(Schema(assumption)))]

    # create new conclusion
    new_conclusion = make_implication(assumption, proof.conclusion)
    # new_proof = Proof(new_proof_assump, new_conclusion, [])
    new_prover = Prover(new_proof_assump, new_conclusion)

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
            new_psi_2 = line_num_conc_dict[make_implication(assumption,psi_2)]
            assert (new_psi_1, new_psi_2)  # check that we found the looked up psi1 and psi2
            conc = make_implication(assumption, l_formula)
            step_1 = new_prover.add_tautological_inference(conc, [new_psi_2, new_psi_1])
            line_num_conc_dict[conc] = step_1
            # (plus(minus(a),plus(a,c))=plus(minus(a),plus(a,c))->((plus(a,c)=a->(plus(minus(a),plus(a,c))=plus(minus(a),plus(a,c))->plus(minus(a),plus(a,c))=plus(minus(a),a)))->plus(minus(a),plus(a,c))=plus(minus(a),a)))
        elif l_type == 'UG':
            # Ax[assumption -> cur] , when x is the same var used in org line
            # we want to make US. but first we need to create with UG the formula of the left side of US
            # let's say KILSHON is Q(), and the original line without UG is R(x). then -
            # 'Q()->R(x)' is already in our lines of proof. we would like to add UG on all and get
            # 'Ax[Q()->R(x)]'. now we will use US and get '(Ax[Q()->R(x)]->(Q()->Ax[R(x)]))'
            # now we will do MP and receive our goal :)
            l_just = proof.lines[line.justification[1]].formula
            ug_base_formula = make_implication(assumption, l_just)  # we have assumption -> cur somewhere
            ug_base_formula_line_number = line_num_conc_dict[ug_base_formula]
            ug_formula = 'A' + l_formula.variable + '[' + ug_base_formula + ']'  # Ax[Q()->R(x)]
            step_1 = new_prover.add_ug(ug_formula, ug_base_formula_line_number)  # Ax[assumption -> R(x)]
            # US = Schema('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'x', 'Q', 'R'})
            print(ug_formula)
            var = str(l_formula.variable)
            instantiation_map = {'x': var, 'Q': str(assumption), 'R': str(ug_formula)}
            us_formula = new_prover.US.instantiate(instantiation_map)
            print('here')
            step_2 = new_prover.add_instantiated_assumption(us_formula, new_prover.US, instantiation_map)
            step_3 = new_prover.add_tautological_inference(str(us_formula.second),[step_1,step_2])
            line_num_conc_dict[us_formula.second] = step_3

    # CASE1 line just is T    sol: T -> assumption -> T ; do MP and we get assumption -> T
    # CASE2 line just is A    solution1: A -> assumption -> A; do MP and we get assumption -> A (when A!=assumption)
                              #solution2:
    # CASE3 line just is MP   solution: find assumption -> (A->B) , find assumption -> A in prev lines
                                        # use tau_inf to get assumption -> B
    # CASE4 line just is UG   solution: add UG  Ax[assumption -> cur] , when x is the same var used in org line
                                        # add US Ax[assumption -> cur] -> (assumption -> Ax[cur])
                                        # add MG to get assumption -> Ax[cur]

            # Task 11.1


def proof_by_contradiction(proof, assumption, print_as_proof_forms=False):
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
