##################################################
#  FILE: testFile.py
#  WRITER : Erez Kaufman, erez, 305605255.
#  EXERCISE : intro2cs ex# 2015-2016
#  DESCRIPTION : 
#
##################################################

from propositions.syntax import Formula

if __name__ == '__main__':
    q = Formula('q')
    z = Formula('z')
    nz = Formula('~',z)
    f = Formula('&',q,z)
    t = Formula('~',f)
    s = '(((~(y10|F)|T)&(F|T))|s2)'
    prefixString = '~|~~&pq2&pq5'
    q = Formula('|',t,f)
    infixTest = Formula.from_infix(s)
    print(infixTest)
    # h = Formula(t,q,f)
    q.from_infix('~(~~(q&r4)|(q&r6))')
    # if q.from_prefix(prefixString ).prefix() == prefixString :
    #     print(q.from_prefix(prefixString ))
    #     print(q.from_prefix(prefixString ).prefix())
    #     print("variables of prefix:", q.from_prefix(prefixString ).variables())
    #
    #     print('variables of q: ', q.variables())
    #
    #     exit(0)

    if q.from_infix(s).infix() == s:
        print(s)
        print(q)
