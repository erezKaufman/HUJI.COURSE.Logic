from propositions.provers import *
import itertools


if __name__ == '__main__':
    # assert prove_implies_self().is_valid()
    test_dict = {}
    # test_dict["d"] = 1
    # test_dict["b"] = 5
    # test_dict["a"] = 3
    # test_dict["c"] = 2
    # lsittt = sorted(test_dict, key=test_dict.get)
    # print(lsittt)
    f = '(p|F)'

    prove_in_model(f)