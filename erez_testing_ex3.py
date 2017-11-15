from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
import itertools

if __name__ == '__main__':
    debug = True
    # Test 2
    a = Formula.from_infix('(~p|q)')
    b = Formula.from_infix('p')
    c = Formula.from_infix('q')
    aa = Formula.from_infix('(~x|y)')
    bb = Formula.from_infix('x')
    cc = Formula.from_infix('y')
    rule = InferenceRule([a, b], c)
    instantiation_map = {'p': Formula.from_infix('x'),
                         'q': Formula.from_infix('y')}
    for assumptions, conclusion, value in [[[aa, bb], cc, True],
                                           [[aa, bb], c, False],
                                           [[aa, b], cc, False],
                                           [[a, bb], cc, False]]:
        candidate = InferenceRule(assumptions, conclusion)
        if debug:
            print('Testing whether', candidate, 'is an instance of', rule)
        assert candidate.is_instance_of(rule) == value
        if value:
            map_ = {}
            assert candidate.is_instance_of(rule, map_)
            assert map_ == instantiation_map
