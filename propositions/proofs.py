""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/proofs.py """

from propositions.syntax import *


class InferenceRule:
    """ An inference rule, i.e., a list of zero or more assumed formulae, and
        a conclusion formula """

    def __init__(self, assumptions, conclusion):
        assert type(conclusion) == Formula
        for assumption in assumptions:
            assert type(assumption) == Formula
        self.assumptions = assumptions
        self.conclusion = conclusion

    def __eq__(self, other):
        if len(self.assumptions) != len(other.assumptions):
            return False
        if self.conclusion != other.conclusion:
            return False
        for assumption1, assumption2 in zip(self.assumptions, other.assumptions):
            if assumption1 != assumption2:
                return False
        return True

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        return str([assumption.infix() for assumption in self.assumptions]) + \
               ' ==> ' + self.conclusion.infix()

    def variables(self):
        """ Return the set of atomic propositions (variables) used in the
            assumptions and in the conclusion of self. """
        return_set = set()
        for assumption in self.assumptions:
            return_set.update(assumption.variables())
        return_set.update(self.conclusion.variables())
        return return_set

    def is_instance_of(self, rule, instantiation_map=None):
        """ Return whether there exist formulae f1,...,fn and variables
            v1,...,vn such that self is obtained by simultaneously substituting
            each occurrence of f1 with v1, each occurrence of f2 with v2, ...,
            in all of the assumptions of rule as well as in its conclusion.
            If so, and if instantiation_map is given, then it is (cleared and)
            populated with the mapping from each vi to the corresponding fi """
        if instantiation_map is None:
            instantiation_map = {}

        for self_assumption, rule_assumption in zip(self.assumptions, rule.assumptions):
            # for  rule_assumption in rule.assumptions:
            if not InferenceRule._update_instantiation_map(self_assumption, rule_assumption, instantiation_map):
                return False
        return InferenceRule._update_instantiation_map(self.conclusion, rule.conclusion, instantiation_map)

    @staticmethod
    def _update_instantiation_map(formula, template, instantiation_map):
        """ Return whether the given formula can be obtained from the given
            template formula by simultaneously and consistantly substituting,
            for every variable in the given template formula, every occurrence
            of this variable with some formula, while respecting the
            correspondence already in instantiation_map (which maps from
            variables to formulae). If so, then instantiation_map is updated
            with any additional substitutions dictated by this matching. If
            not, then instantiation_map may be modified arbitrarily """

        if is_variable(template.root):
            # if we reached the variable in the template, we would like to know if the corresponding formula that we
            # reached after descending the formula tree appears in the instantiation_map as the value for the
            # variable's key
            if template.root not in instantiation_map:
                instantiation_map[template.root] = formula
                return True
            else:
                return instantiation_map[template.root] == formula
        elif is_constant(template.root) and template.root == formula.root:
            return True
        elif is_binary(template.root) and template.root == formula.root:
            first_bool = InferenceRule._update_instantiation_map(formula.first, template.first, instantiation_map)
            second_bool = InferenceRule._update_instantiation_map(formula.second, template.second, instantiation_map)
            if first_bool and second_bool:
                return True
            else:
                instantiation_map.clear()
                return False

        elif is_ternary(template.root) and template.root == formula.root:
            first_bool = InferenceRule._update_instantiation_map(formula.first, template.first, instantiation_map)
            second_bool = InferenceRule._update_instantiation_map(formula.second, template.second, instantiation_map)
            third_bool = InferenceRule._update_instantiation_map(formula.third, template.third, instantiation_map)
            return True if first_bool and second_bool and third_bool else False
        elif is_unary(template.root) and template.root == formula.root:
            first_bool = InferenceRule._update_instantiation_map(formula.first, template.first, instantiation_map)
            return first_bool
        else:
            return False


class DeductiveProof:
    """ A deductive proof, i.e., a statement of an inference rule, a list of
        assumed inference rules, and a list of lines that prove the former from
        the latter """

    class Line:
        """ A line, i.e., a formula, the index of the inference rule whose
            instance justifies the formula from previous lines, and the list
            of indices of these previous lines """

        def __init__(self, conclusion, rule=None, justification=None):
            self.conclusion = conclusion
            self.rule = rule
            self.justification = justification

        def __repr__(self):
            if self.rule is None:
                return self.conclusion.infix()
            r = self.conclusion.infix() + ' (Inference Rule ' + str(self.rule)
            sep = ';'
            for i in range(len(self.justification)):
                r += sep + ' Assumption ' + str(i) + ': Line ' + \
                     str(self.justification[i])
                sep = ','
            r += '.)' if len(self.justification) > 0 else ')'
            return r

    def __init__(self, statement, rules, lines):
        self.statement = statement
        self.rules = rules
        self.lines = lines

    def __repr__(self):
        r = 'Proof for ' + str(self.statement) + ':\n'
        for i in range(len(self.rules)):
            r += 'Inference Rule ' + str(i) + ': ' + str(self.rules[i]) + '\n'
        for i in range(len(self.lines)):
            r += str(i) + ') ' + str(self.lines[i]) + '\n'
        return r

    def instance_for_line(self, line):
        """ Return the instantiated inference rule that corresponds to the
            given line number """

        assumption_list = []
        conclusion = self.lines[line].conclusion
        if self.lines[line].justification is not None:
            for index in self.lines[line].justification:
                assumption_list.append(self.lines[index].conclusion)
        return InferenceRule(assumption_list, conclusion)

    def is_valid(self):
        """ Return whether lines are a valid proof of statement from rules """
        for lineNum in range(0, len(self.lines)):
            # cehck if the number of line is smaller than the numbers in justification
            if self.lines[lineNum].justification is not None:
                if len(self.lines[lineNum].justification) > 0:  # if there are justifications
                    for i in self.lines[lineNum].justification:
                        if i > lineNum:
                            return False
                else:  # else, the list is empty, so we might have a
                    if self.lines[lineNum].rule is None:
                        if self.lines[lineNum].conclusion in self.statement.assumptions:
                            continue
                        else:  # if the conclusion of the line is not in the assumptions of the statement
                            return False

            else:  # if the justification is None, we will check if rule is none. if so than
                if self.lines[lineNum].rule is None:
                    if self.lines[lineNum].conclusion in self.statement.assumptions:
                        continue
                    else:  # if the conclusion of the line is not in the assumptions of the statement
                        return False
            # if self.lines[lineNum].just
            instance = self.instance_for_line(lineNum)
            rule = self.rules[self.lines[lineNum].rule]
            if not instance.is_instance_of(rule):
                return False
        return self.lines[len(self.lines) - 1].conclusion == self.statement.conclusion




def instantiate(formula, instantiation_map):
    """ Return a formula obtained from the given formula by simultaneously
        substituting, for each variable v that is a key of instantiation_map,
        each occurrence v with the formula instantiation_map[v] """
    # Task 5.2.1
    if is_variable(formula.root):
        return instantiation_map[formula.root]
    elif is_constant(formula.root):
        return formula.root
    elif is_unary(formula.root):
        formula.first = instantiate(formula.first, instantiation_map)
    elif is_binary(formula.root):
        formula.first = instantiate(formula.first, instantiation_map)
        formula.second = instantiate(formula.second, instantiation_map)
    elif is_ternary(formula.root):
        formula.first = instantiate(formula.first, instantiation_map)
        formula.second = instantiate(formula.second, instantiation_map)
        formula.third = instantiate(formula.third, instantiation_map)
    return formula


def prove_instance(proof, instance):
    """ Return a proof of the given instance of the inference rule that proof
        proves, via the same inference rules used by proof """
    instantiation_map = {}
    if not instance.is_instance_of(proof.statement, instantiation_map):
        return False

        # for assumption_index in range(len(proof.statement.assumptions)):
        #     if not InferenceRule._update_instantiation_map(instance.assumptions[
        #                                                        assumption_index], proof.statement.assumptions[
        #                                                            assumption_index], instantiation_map):
        #         return False
    assumptions = []
    proof.statement.conclusion = instantiate(proof.statement.conclusion,instantiation_map)
    for assumption_index in range(len(proof.statement.assumptions)):
        assumptions.append(instantiate( proof.statement.assumptions[assumption_index],instantiation_map))
    for rule_index in range(len(proof.rules)):
        proof.rules[rule_index].conclusion = instantiate(proof.rules[rule_index].conclusion,instantiation_map)
        for index in range(len(proof.rules[rule_index].assumptions)):
            proof.rules[rule_index].assumptions[index] = instantiate(proof.rules[rule_index].assumptions[index],instantiation_map)
    for line_num in range(len(proof.lines)):
        proof.lines[line_num].conclusion = instantiate(proof.lines[line_num].conclusion,instantiation_map)
    return proof

def inline_proof(main_proof, lemma_proof):
    """ Return a proof of the inference rule that main_proof proves, via the
        inference rules used in main_proof except for the one proven by
        lemma_proof, as well as via the inference rules used in lemma_proof
        (with duplicates removed) """
    # Task 5.2.2
