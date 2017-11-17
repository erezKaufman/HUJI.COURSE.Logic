from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
import itertools

if __name__ == '__main__':
    debug = True
    DISJUNCTION_COMMUTATIVITY_PROOF = DeductiveProof(
        InferenceRule([Formula.from_infix('(x|y)')], Formula.from_infix('(y|x)')),
        [InferenceRule([Formula.from_infix('(p|q)'), Formula.from_infix('(~p|r)')],
                       Formula.from_infix('(q|r)')),
         InferenceRule([], Formula.from_infix('(~p|p)'))],
        [DeductiveProof.Line(Formula.from_infix('(x|y)')),
         DeductiveProof.Line(Formula.from_infix('(~x|x)'), 1, []),
         DeductiveProof.Line(Formula.from_infix('(y|x)'), 0, [0, 1])])

    print(DISJUNCTION_COMMUTATIVITY_PROOF)

    for line, assumptions, conclusion in [[1, [], '(~x|x)'],
                                          [2, ['(x|y)', '(~x|x)'], '(y|x)']]:
        # if debug:
        #     print('Testing instance for line', line,
        #           'of the following deductive proof:\n' +
        #           str(DISJUNCTION_COMMUTATIVITY_PROOF))
        print(InferenceRule([Formula.from_infix(a) for a in assumptions],
              Formula.from_infix(conclusion)))


    proof = DeductiveProof(InferenceRule([Formula.from_infix('(x|y)')],
                                         Formula.from_infix('(x|y)')),
                           DISJUNCTION_COMMUTATIVITY_PROOF.rules,
                           DISJUNCTION_COMMUTATIVITY_PROOF.lines)
    if debug:
        print('Testing validity of the following deductive proof:\n' + str(proof))
    assert not proof.is_valid()