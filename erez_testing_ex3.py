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
    # for model in listV:
    #     a = [1,2,3,4]
    #     b = [2,3,4,5]
        # print(sorted(model.items(), key = lambda k: k[0]))
        # for key, value in sorted(model.items(), key=lambda k,v: (v, k)):
        #     print( "%s: %s" % (key, value))
        #     model1 = {key: value for key, value in sorted(model.iteritems())}
        # print (sorted(model, key=model.__getitem__))
        # test = {key :value for (key, value) in sorted(model.__getitem__)}
        # print(test)
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