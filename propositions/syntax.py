""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/syntax.py """


def is_variable(s):
    """ Is s an atomic proposition?  """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())


def is_unary(s):
    """ Is s a unary operator? """
    return s == '~'


def is_binary(s):
    """ Is s a binary operator? """
    return s == '&' or s == '|' or s in '-&' or s in '-|' or s  in '->' or s in '<->'

def is_ternary(s):
    """ Is s a ternary operator?"""
    return s == '?:'

def is_constant(s):
    """ Is s a constant? """
    return s == 'T' or s == 'F'


def is_parentheses(s):
    return s == '(' or s == ')'


class Formula:
    """ A Propositional Formula """
    string = ''

    def __init__(self, root, first=None, second=None, third = None):
        """ Create a new formula from its root (a string) and, when needed, the
        first and second operands (each of them a Formula).
        - I added to each object a variable of string to save each time the current state of the formula's string """
        if is_constant(root) or is_variable(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        elif is_binary(root):
            assert type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second
        else:
            assert  is_ternary(root) and type(first) is Formula and type(second) is Formula and type(third) is Formula
            self.root, self.first, self.second, self.third = root, first, second, third

    def __repr__(self):
        return self.infix()

    def __eq__(self, other):
        return self.infix() == other.infix()

    def __ne__(self, other):
        return not self == other

    def infix(self):
        """ Return an infix representation of self """
        if is_constant(self.root) or is_variable(self.root):
            return (self.root)
        elif is_unary(self.root):
            return (self.root) + self.first.infix()

        elif is_binary(self.root):
            return '(' + self.first.infix() + self.root + self.second.infix() + ')'
        else:
            return '(' + self.first.infix() + self.root[0] + self.second.infix() + \
                   self.root[1] + self.third.infix() + ')'

    @staticmethod
    def clean_parentheses(s):
        while is_parentheses(s[0]):
            s = s[1:]
        Formula.string = s
        return s

    @staticmethod
    def build_root(s,is_infix):
        """
        parse for the root
        :param s:
        :return:
        """
        root = ''
        if s[0] == '&' or s[0] =='|':
            root = s[0]
            Formula.string = s[1:]
        elif s[0] == '?':
            root = '?:'
            if is_infix:
                Formula.string = s[1:]
            else:
                Formula.string = s[2:]
        elif s[0] == '-':
            root = s[0:2]
            Formula.string = s[2:]
        elif s[0] == '<':
            root = s[0:3]
            Formula.string = s[3:]
        return root


    @staticmethod
    def from_infix(s):
        """ Return a propositional formula whose infix representation is s """
        Formula.string = s
        if is_constant(s[0]) or is_variable(s[0]):
            #  if the first letter is a variable, we want to check if the next to letters are digits
            return_var = ''
            if len(s) > 1 and s[1].isdigit():
                if len(s) > 2 and s[2].isdigit():
                    Formula.string = s[3:]
                    return_var = s[0:3]
                else:
                    Formula.string = s[2:]
                    return_var = s[0:2]
            else:
                if len(s) > 1:
                    Formula.string = s[1:]
                return_var = s[0]
            return Formula(return_var)
        elif is_unary(s[0]):
            Formula.string = s[1:]
            return Formula(s[0], Formula.from_infix(s[1:]))
        # '(T?F:T)'
        elif is_parentheses(s[0]):
            first = Formula.from_infix(s[1:])
            s = Formula.string
            # remove redundant parentheses
            s = Formula.clean_parentheses(s)

            root = Formula.build_root(s,True)
            s = Formula.string

            second = Formula.from_infix(s)
            if is_ternary(root):
                s = Formula.clean_parentheses(Formula.string)
                third = Formula.from_infix(s[1:])
                return Formula(root, first, second,third)
            return Formula(root, first, second)

    def prefix(self):
        """ Return a prefix representation of self """
        if is_constant(self.root) or is_variable(self.root):
            return (self.root)
        elif is_unary(self.root):
            return (self.root) + self.first.prefix()

        elif is_binary(self.root):
            return self.root + self.first.prefix() + self.second.prefix()
        else:
            return self.root + self.first.prefix() + self.second.prefix()+self.third.prefix()

    @staticmethod
    def from_prefix(s):
        """ Return a propositional formula whose prefix representation is s """
        Formula.string = s
        if is_unary(s[0]):
            Formula.string = s[1:]
            return Formula(s[0], Formula.from_prefix(s[1:]))
        elif is_variable(s[0]) or is_constant(s[0]):
            #  if the first letter is a variable, we want to check if the next to letters are digits
            return_var = ''
            if len(s) > 1 and s[1].isdigit():
                if len(s) > 2 and s[2].isdigit():
                    Formula.string = s[3:]
                    return_var = s[0:3]
                else:
                    Formula.string = s[2:]
                    return_var = s[0:2]
            else:
                if len(s) > 1:
                    Formula.string = s[1:]
                return_var = s[0]
            return Formula(return_var)
        elif is_binary(s[0]):
            root = Formula.build_root(s,False)
            s= Formula.string
            first = Formula.from_prefix(s)
            s = Formula.string
            second = Formula.from_prefix(s)
            return Formula(root, first, second)
        else:
            root = s[0:2]
            first = Formula.from_prefix(s[2:])
            s = Formula.string
            second = Formula.from_prefix(s)
            s = Formula.string
            third = Formula.from_prefix(s)
            return Formula(root,first,second,third)

    def variables(self):
        """ Return the set of atomic propositions (variables) used in self """
        return_set = set()
        if is_variable(self.root):
            return {self.root}
        elif is_unary(self.root):
            return_set.update(self.first.variables())
            return return_set
        elif is_constant(self.root):
            return set()
        else:
            return_set.update(self.first.variables())
            return_set.update(self.second.variables())
            if is_ternary(self.root):
                return_set.update(self.third.variables())
            return return_set



