""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/some_proofs.py """

from predicates.prover import *


def lovers_proof(print_as_proof_forms=False):
    """ Return a proof that from assumptions (in addition to Prover.AXIOMS):
        1) Everybody loves somebody and
        2) Everybody loves a lover
        derives the conclusion:
        Everybody loves everybody.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover(['Ax[Ey[Loves(x,y)]]',
                     'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'],
                    'Ax[Az[Loves(z,x)]]', print_as_proof_forms)
    # Task 10.4
    step_1 = prover.add_assumption('Ax[Ey[Loves(x,y)]]') # assumption 1
    step_2 = prover.add_assumption('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]') # assumption 2
    step_3 = prover.add_universal_instantiation('Ey[Loves(x,y)]', step_1, 'x') # use task_1 to remove Ax
    step_4 = prover.add_universal_instantiation('Az[Ay[(Loves(x,y)->Loves(z,x))]]', step_2, 'x') # remove Ey
    step_5 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step_4, 'z') # remove Az
    step_6 = prover.add_universal_instantiation('(Loves(x,y)->Loves(z,x))', step_5, 'y') # remove Ay
    step_7 = prover.add_existential_derivation('Loves(z,x)', step_3, step_6) # conclude Loves(z,x) using task_3
    step_8 = prover.add_ug('Az[Loves(z,x)]', step_7) # add Az using UG
    step_9 = prover.add_ug('Ax[Az[Loves(z,x)]]', step_8) # add Ax using UG
    return prover.proof
#test

def homework_proof(print_as_proof_forms=False):
    """ Return a proof that from the assumptions (in addition to Prover.AXIOMS):
        1) No homework is fun, and
        2) Some reading is homework
        derives the conclusion:
        Some reading is not fun.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover(['~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'],
                    'Ex[(Reading(x)&~Fun(x))]', print_as_proof_forms)
    # Task 10.5
    step_1 = prover.add_assumption('~Ex[(Homework(x)&Fun(x))]') # given assumption
    step_2 = prover.add_assumption('Ex[(Homework(x)&Reading(x))]') # given assumption
    inst_dict = {'R(x)': '(Homework(x)&Fun(x))', 'c': 'x', 'x': 'x'}
    # using inst_assumption on EI we get H(x)&F(x)->Ex[H(x)&F(x)]
    step_3 = prover.add_instantiated_assumption('((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])', Prover.EI,
                                                inst_dict)
    # using tauto_inf on step_3 we get the not version of step_3
    step_4 = prover.add_tautological_inference('(~Ex[(Homework(x)&Fun(x))]->~(Homework(x)&Fun(x)))', [step_3])
    step_5 = prover.add_mp('~(Homework(x)&Fun(x))', step_1, step_4) # get ~H(x)&F(x) using MP
    # adding another tau_inf based on step_4
    step_6 = prover.add_tautological_inference('(~(Homework(x)&Fun(x))->(Homework(x)->~Fun(x)))', [step_4])
    s_7_inst_dict = {'R(x)': '(Reading(x)&~Fun(x))', 'c': 'x'}
    # using inst_assumption on EI we get R(x)&~F(x)->Ex[R(x)&~F(x)]
    step_7 = prover.add_instantiated_assumption('((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])', Prover.EI,
                                                s_7_inst_dict)
    step_8 = prover.add_mp('(Homework(x)->~Fun(x))', step_5, step_6) # get H(x)->~F(x) using mp
    # use tau_inf on step 6 and step 8 to get H(x)&R(x)->R(x)&~F(x)
    step_9 = prover.add_tautological_inference('((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))', [step_6, step_8])
    # se tau_inf on step 7 and step 8 to get H(x)&R(x)->Ex[R(x)&F(x)]
    step_10 = prover.add_tautological_inference('((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])',
                                                [step_7, step_9])
    # finally conclude what we want using existential_derivation on the second assumption (step_2) and the last step
    step_11 = prover.add_existential_derivation('Ex[(Reading(x)&~Fun(x))]', step_2, step_10)
    return prover.proof


GROUP_AXIOMS = ['plus(0,x)=x', 'plus(minus(x),x)=0',
                'plus(plus(x,y),z)=plus(x,plus(y,z))']


def unique_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the group axioms (in addition to Prover.AXIOMS)
        and from the assumption a+c=a proves c=0. The Boolean flag
        print_as_proof_forms specifies whether the proof being constructed is
        to be printed in real time as it is being constructed """
    prover = Prover(GROUP_AXIOMS + ['plus(a,c)=a'], 'c=0', print_as_proof_forms)
    step_1 = prover.add_assumption('plus(a,c)=a') # given assumption
    # using the v_termed plus(minus(a),v) we get -> -a +(a+c) = -a +a
    step_2 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),a)', step_1, 'plus(minus(a),v)')
    step_3 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))') # third group axiom
    # input (-a+a)+c=-a+(a+c) using free_inst
    step_4 = prover.add_free_instantiation('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))', step_3,
                                           {'x': 'minus(a)', 'y': 'a', 'z': 'c'})
    # conclude (-a+a)+c=-a+a using chained_equality of step_2 and step_4
    step_5 = prover.add_chained_equality('plus(plus(minus(a),a),c)=plus(minus(a),a)', [step_4, step_2])
    step_6 = prover.add_assumption('plus(minus(x),x)=0') # second group axiom
    step_7 = prover.add_free_instantiation('plus(minus(a),a)=0', step_6, {'x': 'a'})  # input -a+a=0 using free_inst
    # using v_termed plus(v,c) we get -> (-a+a)+c = 0+c
    step_8 = prover.add_substituted_equality('plus(plus(minus(a),a),c)=plus(0,c)', step_7, 'plus(v,c)')
    step_9 = prover.add_flipped_equality('plus(0,c)=plus(plus(minus(a),a),c)', step_8) # flip 8 -> 0+c=(-a+a)+c
    # conclude 0+c=0 using chained_equality of step_9, step_5, and step_7
    step_10 = prover.add_chained_equality('plus(0,c)=0', [step_9, step_5, step_7])
    step_11 = prover.add_assumption('plus(0,x)=x') # first group assumption
    step_12 = prover.add_free_instantiation('plus(0,c)=c', step_11, {'x': 'c'}) # we get 0+c=c using free_inst
    step_13 = prover.add_flipped_equality('c=plus(0,c)', step_12) # flip 12 -> c=0+c
    step_14 = prover.add_chained_equality('c=0', [step_13, step_10]) # conclude c=0 using chained on step 13, step 10
    # Task 10.10
    return prover.proof

FIELD_AXIOMS = GROUP_AXIOMS + ['plus(x,y)=plus(y,x)', 'times(x,1)=x',
                               'times(x,y)=times(y,x)',
                               'times(times(x,y),z)=times(x,times(y,z))',
                               '(~x=0->Ey[times(y,x)=1])',
                               'times(x,plus(y,z))=plus(times(x,y),times(x,z))']

def multiply_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the field axioms (in addition to Prover.AXIOMS)
        proves 0*x=0. The Boolean flag print_as_proof_forms specifies whether
        the proof being constructed is to be printed in real time as it is
        being constructed """
    prover = Prover(FIELD_AXIOMS, 'times(0,x)=0', print_as_proof_forms)
    # Task 10.11
    step_1 = prover.add_assumption('times(x,y)=times(y,x)')
    step_2 = prover.add_free_instantiation('times(0,x)=times(x,0)', step_1, {'x': '0', 'y': 'x'})  # #1 in chained!
    step_3 = prover.add_assumption('plus(0,x)=x')
    step_4 = prover.add_free_instantiation('plus(0,times(x,0))=times(x,0)', step_3, {'x': 'times(x,0)'})
    step_5 = prover.add_flipped_equality('times(x,0)=plus(0,times(x,0))', step_4)  # x*0=0+x*0 # #2 in chained!
    step_6 = prover.add_assumption('plus(minus(x),x)=0')  # -0*x+0*x=0
    step_7 = prover.add_free_instantiation('plus(minus(times(x,0)),times(x,0))=0', step_6, {'x': 'times(x,0)'})
    step_8 = prover.add_substituted_equality('plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(0,times(x,0))',
                                             step_7, 'plus(v,times(x,0))')
    step_9 = prover.add_flipped_equality('plus(0,times(x,0))=plus(plus(minus(times(x,0)),times(x,0)),times(x,0))',
                                         step_8)  # #3 in chained!
    step_10 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    step_11 = prover.add_free_instantiation(
        'plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(minus(times(x,0)),plus(times(x,0),times(x,0)))',
        step_10, {'x': 'minus(times(x,0))', 'y': 'times(x,0)', 'z': 'times(x,0)'})  # #4 in chained!
    # now we want to add the line that says - x*(0+0) = x*0.
    # We will take the assumption (x*(y+z)=x*y+y*z), flip it, and insert 0's in y,z. I will get that x*0+x*0=x*(0+0)
    step_12 = prover.add_assumption('times(x,plus(y,z))=plus(times(x,y),times(x,z))')
    step_13 = prover.add_free_instantiation(
        'times(x,plus(0,0))=plus(times(x,0),times(x,0))',
        step_12, {'x': 'x', 'y': '0', 'z': '0'})
    step_14 = prover.add_flipped_equality('plus(times(x,0),times(x,0))=times(x,plus(0,0))', step_13)
    # Now We want to add the line that says - 'x*(0+0)=x*0.
    # We add the assumption 0+x=x and insert 0 as x.
    # after that we substitute each side of the equation with 'times(x,v) and get what we want.
    step_15 = prover.add_assumption('plus(0,x)=x')
    step_16 = prover.add_free_instantiation('plus(0,0)=0', step_15, {'x': '0'})
    step_17 = prover.add_substituted_equality('times(x,plus(0,0))=times(x,0)', step_16, 'times(x,v)')
    # We now chain step 14 with the step 17 and then substitute term 'plus(minus(times(x,0),v)' and will get:
    # 'plus(minus(times(x,0)),plus(times(x,0),times(x,0)))=plus(minus(times(x,0)),times(x,0))'
    step_18 = prover.add_chained_equality('plus(times(x,0),times(x,0))=times(x,0)', [step_14, step_17])
    step_19 = prover.add_substituted_equality(
        'plus(minus(times(x,0)),plus(times(x,0),times(x,0)))=plus(minus(times(x,0)),times(x,0))',
        step_18, 'plus(minus(times(x,0)),v)')  # #5 in chained!
    # sanity check - we have now -x*0 +x*0- and we want to do -x*0+x*0=0 and chain it all together
    step_20 = prover.add_free_instantiation('plus(minus(times(x,0)),times(x,0))=0',
                                            step_6, {'x': 'times(x,0)'})  # #6 in chained!
    step_21 = prover.add_chained_equality('times(0,x)=0', [step_2, step_5, step_9, step_11, step_19, step_20])
    return prover.proof


PEANO_AXIOMS = ['(s(x)=s(y)->x=y)', '(~x=0->Ey[s(y)=x])', '~s(x)=0',
                'plus(x,0)=x', 'plus(x,s(y))=s(plus(x,y))', 'times(x,0)=0',
                'times(x,s(y))=plus(times(x,y),x)',
                Schema('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])', 'R')]


def peano_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the Peano axioms (in addition to Prover.AXIOMS)
        proves 0+x=x. The Boolean flag print_as_proof_forms specifies whether
        the proof being constructed is to be printed in real time as it is
        being constructed """
    prover = Prover(PEANO_AXIOMS, 'plus(0,x)=x', print_as_proof_forms)
    # Task 10.12
    step_1 = prover.add_assumption('plus(x,0)=x') # add assumption
    step_2 = prover.add_assumption('plus(x,s(y))=s(plus(x,y))')

    step_3 = prover.add_free_instantiation("plus(0,0)=0", step_1, {'x': '0'})
    step_4 = prover.add_instantiated_assumption("(plus(0,x)=x->(plus(0,s(x))=s(plus(0,x))->plus(0,s(x))=s(x)))",
                                                Prover.ME, {'R(v)': 'plus(0,s(x))=s(v)', 'c': 'plus(0,x)', 'd': 'x'})
    step_5 = prover.add_free_instantiation("plus(0,s(x))=s(plus(0,x))", step_2, {'x': '0', 'y': 'x'})
    step_6 = prover.add_tautological_inference('(plus(0,x)=x->plus(0,s(x))=s(x))', [step_5, step_4])
    step_7 = prover.add_ug('Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]', step_6)
    step_8 = prover.add_tautological_inference('(plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])', [step_3, step_7])
    step_9 = prover.add_instantiated_assumption('((plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])->Ax[plus(0,x)=x])',
                                                PEANO_AXIOMS[7], {'R(v)': 'plus(0,v)=v'})
    step_10 = prover.add_mp('Ax[plus(0,x)=x]', step_8, step_9)
    step_11 = prover.add_universal_instantiation(str(prover.proof.conclusion), step_10, 'x')
    return prover.proof


COMPREHENSION_AXIOM = Schema('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]', {'R'})


def russell_paradox_proof(print_as_proof_forms=False):
    """ Return a proof that from the axiom schema of (unrestricted)
        comprehension (in addition to Prover.AXIOMS) proves the falsehood
        (z=z&~z=z). The Boolean flag print_as_proof_forms specifies whether the
        proof being constructed is to be printed in real time as it is being
        constructed """
    prover = Prover([COMPREHENSION_AXIOM], '(z=z&~z=z)', print_as_proof_forms)
    # Task 10.13
    step_1 = prover.add_instantiated_assumption('Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]',COMPREHENSION_AXIOM,
                                                {'R(v)' : '~In(v,v)'}) # add the assumption with R(v) as ~In(v,v)
    # using the UI axium, add an instantiated assumption such that R(v):((In(v,y)->~In(v,v))&(~In(v,v)->In(v,y)))
    step_2 = prover.add_instantiated_assumption(
        '(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y))))',Prover.UI,
        {'x': 'x', 'c': 'y', 'R(v)': '((In(v,y)->~In(v,v))&(~In(v,v)->In(v,y)))'})
    # the right side (our conclusion) is a contradiction, then the following line is a tautology
    step_3 = prover.add_tautology('(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(z=z&~z=z))')
    # using steps 2 and 3 we can conclude the following line using tautological_inference
    step_4 = prover.add_tautological_inference('(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->(z=z&~z=z))',
                                               [step_2,step_3])
    # finally, using existential_derivation we on the assumption and step_4 we reach the conclusion
    step_5 = prover.add_existential_derivation('(z=z&~z=z)',step_1,step_4)
    return prover.proof

