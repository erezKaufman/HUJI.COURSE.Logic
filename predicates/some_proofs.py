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
    step_1 = prover.add_assumption('Ax[Ey[Loves(x,y)]]')
    step_2 = prover.add_assumption('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]')
    step_3 = prover.add_universal_instantiation('Ey[Loves(x,y)]', step_1, 'x')
    step_4 = prover.add_universal_instantiation('Az[Ay[(Loves(x,y)->Loves(z,x))]]', step_2, 'x')
    step_5 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step_4, 'z')
    step_6 = prover.add_universal_instantiation('(Loves(x,y)->Loves(z,x))', step_5, 'y')
    step_7 = prover.add_existential_derivation('Loves(z,x)', step_3, step_6)
    step_8 = prover.add_ug('Az[Loves(z,x)]', step_7)
    step_9 = prover.add_ug('Ax[Az[Loves(z,x)]]', step_8)
    return prover.proof

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
    step_1 = prover.add_assumption('~Ex[(Homework(x)&Fun(x))]')
    step_2 = prover.add_assumption('Ex[(Homework(x)&Reading(x))]')
    inst_dict = {'R(x)':'(Homework(x)&Fun(x))', 'c':'x', 'x':'x'}
    step_3 = prover.add_instantiated_assumption('((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])', Prover.EI ,inst_dict)
    step_4 = prover.add_tautological_inference('(~Ex[(Homework(x)&Fun(x))]->~(Homework(x)&Fun(x)))', [step_3])
    step_5 = prover.add_mp('~(Homework(x)&Fun(x))', step_1,step_4)
    step_6 = prover.add_tautological_inference('(~(Homework(x)&Fun(x))->(Homework(x)->~Fun(x)))', [step_4])
    s_7_inst_dict = {'R(x)':'(Reading(x)&~Fun(x))', 'c':'x'}
    step_7 = prover.add_instantiated_assumption('((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])', Prover.EI , s_7_inst_dict)
    step_8 = prover.add_mp('(Homework(x)->~Fun(x))', step_5,step_6)
    step_9 = prover.add_tautological_inference('((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))', [step_6,step_8])
    step_10 = prover.add_tautological_inference('((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])', [step_7,step_9])
    step_11 = prover.add_existential_derivation('Ex[(Reading(x)&~Fun(x))]', step_2,step_10)
    return prover.proof


GROUP_AXIOMS = ['plus(0,x)=x', 'plus(minus(x),x)=0',
                'plus(plus(x,y),z)=plus(x,plus(y,z))']

ZERO = Schema('plus(0,x)=x',{'x'})
NEGATE = Schema('plus(minus(x),x)=0',{'x'})
COMMUTATIVE = Schema('plus(plus(x,y),z)=plus(x,plus(y,z))',{'x','y','z'})


def unique_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the group axioms (in addition to Prover.AXIOMS)
        and from the assumption a+c=a proves c=0. The Boolean flag
        print_as_proof_forms specifies whether the proof being constructed is
        to be printed in real time as it is being constructed """
    prover = Prover(GROUP_AXIOMS + ['plus(a,c)=a'], 'c=0', print_as_proof_forms)
    step_1 = prover.add_assumption('plus(a,c)=a')
    step_2 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),a)',step_1,'plus(minus(a),v)')
    step_3 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    step_4 = prover.add_free_instantiation('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))', step_3, {'x': 'minus(a)', 'y': 'a', 'z': 'c'})
    step_5 = prover.add_flipped_equality('plus(minus(a),a)=plus(minus(a),plus(a,c))',step_2)
    step_6 = prover.add_flipped_equality('plus(minus(a),plus(a,c))=plus(plus(minus(a),a),c)',step_4)
    step_7 = prover.add_chained_equality('plus(minus(a),a)=plus(plus(minus(a),a),c)',[step_5,step_6]) # -a+a = (-a+a)+c
    step_8 = prover.add_assumption('plus(minus(x),x)=0')
    step_9 = prover.add_free_instantiation('plus(minus(a),a)=0', step_8, {'x':'a'})
    step_10 = prover.add_flipped_equality('0=plus(minus(a),a)',step_9) # 0 = -a+a
    step_11 = prover.add_chained_equality('0=plus(plus(minus(a),a),c)',[step_10,step_7]) # 0 = (-a+a)+c





    # instantiate step 4 with step 2
    # after step_5 we instantiate  {'x': 'minus(a)', 'y': 'a', 'z': 'c'}  and get plus(minus(a),a)=plus(minus(a),
    # plus(a,c))
    # step_6 = # assumption GROUP[1] -a+a=0
    # step_7 = #
    # prover.add_instantiated_assumption()
    # Task 10.10
    return prover.proof

    # prover = Prover(GROUP_AXIOMS + ['plus(a,c)=a'], 'c=0', print_as_proof_forms)
    # step_1 = prover.add_assumption('plus(a,c)=a')
    # step_2 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),a)', step_1, 'plus(minus(a),v)')
    # # after step 2 we have 'plus(minus(a),plus(a,c))=plus(minus(a),a)' => (-a)+(a+c)=(-a)+a
    #
    # # step_3 = prover.add_assumption(GROUP_AXIOMS[2])# assumption GROUP[2]
    # #  after step_3 we have an assumption of plus(plus(x,y),z)=plus(x,plus(y,z)) => (x+y)+z= x+(y+z)
    # # step_4 = prover.add_flipped_equality('plus(x,plus(y,z))=plus(plus(x,y),z)',step_3)# flipped step3
    # step_4 = prover.add_flipped_equality('plus(minus(a),a)=plus(minus(a),plus(a,c))', step_2)  # flipped step3
    #
    # # after step_4 we have 'plus(x,plus(y,z))=plus(plus(x,y),z)' => (x+(y+z)=(x+y)+z
    # # after step_4 we have 'plus(x,plus(y,z))=plus(plus(x,y),z)' => (x+(y+z)=(x+y)+z
    # step_5 = prover.add_instantiated_assumption('plus(minus(a),a)=plus(minus(a),plus(minus(a),plus(a,c))',
    #                                             prover.proof.assumptions[8], {'x': 'minus(a)',
    #                                                                           'y': 'a', 'z': 'c'})
    # # instantiate step 4 with step 2
    # # after step_5 we instantiate  {'x': 'minus(a)', 'y': 'a', 'z': 'c'}  and get plus(minus(a),a)=plus(minus(a),
    # # plus(a,c))
    # # step_6 = # assumption GROUP[1] -a+a=0
    # # step_7 = #
    # # prover.add_instantiated_assumption()
    # # Task 10.10
    # return prover.proof

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
    return prover.proof

if __name__ == '__main__':
    pass
    # f = Formula.parse('((Ay[(Loves(x,y)->Loves(z,x))]&Ey[Loves(x,y)])->Loves(z,x))')
    # print(f.root)