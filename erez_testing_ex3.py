from propositions.syntax import *
from propositions.semantics import *
import itertools

if __name__ == '__main__':
    f = '|&&||||&~|&|&|w6r3y10F|FTp7F&t1r5TFT|q2t7z1&u9F'
    q = '((r&(q|~p))|(p&q))'
    h = '(p?q:r)'
    t = '?:'+f+q+h
    a = '(p<->p)'
    # print(Formula.from_infix(a))
    # 	Or(a = ((p&q)|((q&r)|~p)), out = out);
    print_truth_table(Formula.from_infix(h))
    print_truth_table(Formula.from_infix(q))

    # And(a=r, b=p, out=bAndsel);p&r
    # Not( in = p, out = notsel); ~p
    # Or(a=r, b=~p, out=bOrNotsel); r|~p
    # And(a=q, b=bOrNotsel, out=aAndbOrNotsel); (q&(r|~p))
    # Or(a=(p&r), b=(q&(r|~p)), out=out);