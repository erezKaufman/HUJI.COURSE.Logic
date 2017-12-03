from propositions.provers import *
from propositions.semantics import *
import itertools


if __name__ == '__main__':
    # assert prove_implies_self().is_valid()
    f = Formula.from_infix('((~p->~q)->((~p->q)->p))')
    gV = all_models(sorted(list(f.variables())))
    listV = list(gV)
    # test = sorted(listV, key=lambda k: k['p'])
    print(listV)
    assumption = [Formula.from_infix('(p&q)')]
    rule = InferenceRule(assumption, Formula.from_infix('(p|q)'))
    result = {'q': False, 'p': False}
    assert not evaluate_inference(rule, result)
    # newlist = sorted(listV,key=listV)
    # print(sorted(listV),)


    # test_dict = {}
    # test_dict["d"] = 1
    # test_dict["b"] = 5
    # test_dict["a"] = 3
    # test_dict["c"] = 2
    # lsittt = sorted(test_dict, key=test_dict.get)
    # print(lsittt)
    # f = '(p|F)'

    # prove_in_model(f)