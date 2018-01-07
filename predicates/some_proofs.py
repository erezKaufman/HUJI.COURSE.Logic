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
    inst_dict = {'R(x)': '(Homework(x)&Fun(x))', 'c': 'x', 'x': 'x'}
    step_3 = prover.add_instantiated_assumption('((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])', Prover.EI,
                                                inst_dict)
    step_4 = prover.add_tautological_inference('(~Ex[(Homework(x)&Fun(x))]->~(Homework(x)&Fun(x)))', [step_3])
    step_5 = prover.add_mp('~(Homework(x)&Fun(x))', step_1, step_4)
    step_6 = prover.add_tautological_inference('(~(Homework(x)&Fun(x))->(Homework(x)->~Fun(x)))', [step_4])
    s_7_inst_dict = {'R(x)': '(Reading(x)&~Fun(x))', 'c': 'x'}
    step_7 = prover.add_instantiated_assumption('((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])', Prover.EI,
                                                s_7_inst_dict)
    step_8 = prover.add_mp('(Homework(x)->~Fun(x))', step_5, step_6)
    step_9 = prover.add_tautological_inference('((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))', [step_6, step_8])
    step_10 = prover.add_tautological_inference('((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])',
                                                [step_7, step_9])
    step_11 = prover.add_existential_derivation('Ex[(Reading(x)&~Fun(x))]', step_2, step_10)
    return prover.proof


GROUP_AXIOMS = ['plus(0,x)=x', 'plus(minus(x),x)=0',
                'plus(plus(x,y),z)=plus(x,plus(y,z))']


# ZERO = Schema('plus(0,x)=x',{'x'})
# NEGATE = Schema('plus(minus(x),x)=0',{'x'})
# COMMUTATIVE = Schema('plus(plus(x,y),z)=plus(x,plus(y,z))',{'x','y','z'})


def unique_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the group axioms (in addition to Prover.AXIOMS)
        and from the assumption a+c=a proves c=0. The Boolean flag
        print_as_proof_forms specifies whether the proof being constructed is
        to be printed in real time as it is being constructed """
    # a+c=a => plus(a,c)=a => plus(minus(a),plus(a,c))=plus(minus(a),a) {-a +(a+c)= -a+a} =>
    # => plus(plus(minus(a),a),c))=plus(minus(a),a) {(-a+a)+c = -a+a}
    # let's stop now and take plus(minus(x),x)=0 => plus(minus(a),a)=0
    # I want to set plus(plus(minus(a),a),c)= plus(0,c) - I will do that by substitute the former step with 'plus(v,c)'
    # I will now have plus(plus(minus(a),a),c)= plus(0,c) and plus(plus(minus(a),a),c)=plus(minus(a),a)
    # I will flip plus(plus(minus(a),a),c)= plus(0,c) to be  plus(0,c)=plus(plus(minus(a),a),c) and now chain it to get
    # plus(0,c)=plus(minus(a),a)
    # Again, use the axiom plus(minus(x),x)=0 and get plus(minus(a),a)=0 and so we have plus(0,c)=0
    # another axiom, and plus(0,c)=c, then c = 0
    # -a +(a+c)= -a+a => plus(minus(a),plus(a,c))=plus(minus(a),a)
    # (-a+a)+c = -a+a => plus(plus(minus(a),a),c)=plus(minus(a),a)
    #  plus(minus(x),x)=0 :

    prover = Prover(GROUP_AXIOMS + ['plus(a,c)=a'], 'c=0', print_as_proof_forms)

    step_1 = prover.add_assumption('plus(a,c)=a')
    # -a +(a+c) = -a +a
    step_2 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),a)', step_1, 'plus(minus(a),v)')
    # (-a+a)+c=-a+(a+c)
    step_3 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    step_4 = prover.add_free_instantiation('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))', step_3,
                                           {'x': 'minus(a)', 'y': 'a', 'z': 'c'})
    # step5e = prover.add_flipped_equality('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))',step_4)

    step5e = prover.add_chained_equality('plus(plus(minus(a),a),c)=plus(minus(a),a)', [step_4, step_2])  # (-a+a)+c=-a+a
    step6e = prover.add_assumption('plus(minus(x),x)=0')
    step7e = prover.add_free_instantiation('plus(minus(a),a)=0', step6e, {'x': 'a'})  # -a+a=0
    step8e = prover.add_substituted_equality('plus(plus(minus(a),a),c)=plus(0,c)', step7e, 'plus(v,c)')
    step9e = prover.add_flipped_equality('plus(0,c)=plus(plus(minus(a),a),c)', step8e)
    step10e = prover.add_chained_equality('plus(0,c)=0', [step9e, step5e, step7e])
    step11e = prover.add_assumption('plus(0,x)=x')
    step12e = prover.add_free_instantiation('plus(0,c)=c', step11e, {'x': 'c'})
    step13e = prover.add_flipped_equality('c=plus(0,c)', step12e)
    step14e = prover.add_chained_equality('c=0', [step13e, step10e])

    # prover = Prover(GROUP_AXIOMS + ['plus(a,c)=a'], 'c=0', print_as_proof_forms)
    # step_1 = prover.add_assumption('plus(a,c)=a')
    # step_2 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),a)', step_1, 'plus(minus(a),v)')
    # step_3 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    # step_4 = prover.add_free_instantiation('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))', step_3,
    #                                        {'x': 'minus(a)', 'y': 'a', 'z': 'c'})
    # step_5 = prover.add_flipped_equality('plus(minus(a),a)=plus(minus(a),plus(a,c))', step_2)
    # step_6 = prover.add_flipped_equality('plus(minus(a),plus(a,c))=plus(plus(minus(a),a),c)', step_4)
    # step_7 = prover.add_chained_equality('plus(minus(a),a)=plus(plus(minus(a),a),c)',
    #                                      [step_5, step_6])  # -a+a = (-a+a)+c
    # step_8 = prover.add_assumption('plus(minus(x),x)=0')
    # step_9 = prover.add_free_instantiation('plus(minus(a),a)=0', step_8, {'x': 'a'})  # -a+a=0
    # step_10 = prover.add_flipped_equality('0=plus(minus(a),a)', step_9)  # 0 = -a+a
    # step_11 = prover.add_chained_equality('0=plus(plus(minus(a),a),c)', [step_10, step_7])  # 0 = (-a+a)+c
    # step_12 = prover.add_flipped_equality('plus(plus(minus(a),a),c)=0', step_11)  # (-a+a)+c = 0
    # # this line won't work because you try to make '0=plus(minus(a),a)' => 'plus(plus(minus(a),a),c)=0' and there is
    # # nothing that connects them together. you also need to add 'c' in the right side of the equation
    # step_13 = prover.add_chained_equality('plus(0,c)=c',
    #                                       [step_10, step_12])  # 0+c = 0 #TODO this line doesnt really work
    #
    # step_13_5 = prover.add_flipped_equality('c=plus(0,c)', step_13)  # 0=0+c
    # step_14 = prover.add_assumption('plus(0,x)=x')
    # step_15 = prover.add_free_instantiation('plus(0,c)=c', step_14, {'x': 'c'})  # 0+c=c
    # step_16 = prover.add_chained_equality('0=c', [step_13_5, step_15])  # 0=c
    # step_17 = prover.add_chained_equality('c=0', step_16)  # c=0

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
    # step_1 = times(x,y)=times(y,x) => x*0 = 0*x
    # step_2 = 0*x = 0+0*x =>
    # step_3 = (-0*x+0*x) + 0*x = -0*x+(0*x + 0*x)
    # step_4 = -0*x+(0*x + 0*x) = -0*x + (0+0)*x
    # step_5 = -0*x + x*(0+0) = -0*x + 0*x
    # step_6 = 0*x-0*x=0
    # step_7 chained equality
    step_1 = prover.add_assumption('times(x,y)=times(y,x)')
    step_2 = prover.add_free_instantiation('times(0,x)=times(x,0)', step_1, {'x': '0', 'y': 'x'})  # #1 in chained!
    step_3 = prover.add_assumption('plus(0,x)=x')
    step_4 = prover.add_free_instantiation('plus(0,times(x,0))=times(x,0)', step_3, {'x': 'times(x,0)'})
    step_5 = prover.add_flipped_equality('times(x,0)=plus(0,times(x,0))', step_4)  # x*0=0+x*0 # #2 in chained!
    step_6 = prover.add_assumption('plus(minus(x),x)=0')  # -0*x+0*x=0
    step_7 = prover.add_free_instantiation('plus(minus(times(x,0)),times(x,0))=0', step_6, {'x': 'times(x,0)'})
    step_8 = prover.add_substituted_equality('plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(0,times(x,0))',
                                             step_7,
                                             'plus(v,times(x,0))')
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
    step1 = prover.add_assumption(PEANO_AXIOMS[0])
    step2 = prover.add_assumption(PEANO_AXIOMS[1])
    step3 = prover.add_assumption(PEANO_AXIOMS[2])
    step4 = prover.add_assumption(PEANO_AXIOMS[3])
    step5 = prover.add_assumption(PEANO_AXIOMS[4])
    step6 = prover.add_assumption(PEANO_AXIOMS[5])
    step7 = prover.add_assumption(PEANO_AXIOMS[6])

    step10 = prover.add_free_instantiation("plus(0,0)=0", step4, {'x': '0'})
    step11 = prover.add_instantiated_assumption("(plus(0,x)=x->(plus(0,s(x))=s(plus(0,x))->plus(0,s(x))=s(x)))",
                                                Prover.ME, {'R(v)': 'plus(0,s(x))=s(v)', 'c': 'plus(0,x)', 'd': 'x'})
    step12 = prover.add_free_instantiation("plus(0,s(x))=s(plus(0,x))", step5, {'x': '0', 'y': 'x'})
    step13 = prover.add_tautological_inference('(plus(0,x)=x->plus(0,s(x))=s(x))', [step12, step11])
    step14 = prover.add_ug('Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]', step13)
    step15 = prover.add_tautological_inference('(plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])', [step10, step14])
    step16 = prover.add_instantiated_assumption('((plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])->Ax[plus(0,x)=x])',
                                                prover.proof.assumptions[13], {'R(v)': 'plus(0,v)=v'})
    step17 = prover.add_mp('Ax[plus(0,x)=x]', step15, step16)
    step18 = prover.add_universal_instantiation(str(prover.proof.conclusion), step17, 'x')
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
    # step_1 = prover.add_assumption(COMPREHENSION_AXIOM.formula)
    step_2 = prover.add_instantiated_assumption(
        '(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->((In(y,y)->~In(y,y))&(~In(y,y->In(y,y)))))',Prover.UI,
        # UI => Ax[R(x)]->R(c)
        # R(x) => ((In(x,y)->~In(x,y))&(~In(x,y->In(x,y)))
        {'x': 'x', 'c': 'y', 'R(v)': '((In(v,y)->~In(v,y))&(~In(v,y)->In(v,y)))'})
    # step_3 = prover.add_free_instantiation(
    #     '(Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]->((In(y,y)->∼In(y,y))&(∼In(y,y)->In(y,y))))',
    #     0,{'x':'x', 'c' : 'y', 'R(v)': '~In(v,y)'})
    # step_3 = add_free... with map {'x':'x', 'c' : 'y', 'R(v)': '~In(v,y)'}
    # (Ax[((In(x, y) → R(x))&(R(x) → In(x, y)))] → ((In (y, y) →∼ In (y, y)) & ( ∼ In (y, y) → In (y, y))))
    #     UI = Schema('(Ax[R(x)]->R(c))', {'R', 'x', 'c'})
    step_4 = prover.add_tautology('((In(y, y)->~In(y, y)) & ((~In(y, y)->In(y, y))->(z = z & ~z = z)))')
    # step_5 =

    return prover.proof


if __name__ == '__main__':
    pass
    # f = Formula.parse('((Ay[(Loves(x,y)->Loves(z,x))]&Ey[Loves(x,y)])->Loves(z,x))')
    # print(f.root)
