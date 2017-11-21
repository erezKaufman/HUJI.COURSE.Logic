from propositions.provers import *
import itertools

if __name__ == '__main__':
    assert prove_implies_self().is_valid()