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
        if len(self.assumptions) != len(rule.assumptions):
            return False
        for self_assumption, rule_assumption in zip(self.assumptions, rule.assumptions):
            # for  rule_assumption in rule.assumptions:
            if not InferenceRule._update_instantiation_map(self_assumption, rule_assumption, instantiation_map):
                return False
        return InferenceRule._update_instantiation_map(self.conclusion, rule.conclusion, instantiation_map)

    @staticmethod
    def _update_instantiation_map(formula: Formula, template: Formula, instantiation_map: dict):
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
        for lineNum,line in enumerate(self.lines):
             # cehck if the number of line is smaller than the numbers in justification
            if line.justification is not None:
                if len(line.justification) > 0:  # if there are justifications
                    for i in line.justification:
                        if i > lineNum:
                            print("1",lineNum) #TODO DELETE ME
                            return False
                else:  # else, the list is empty, so we might have a
                    if line.rule is None:
                        if line.conclusion in self.statement.assumptions:
                            continue
                        else:  # if the conclusion of the line is not in the assumptions of the statement
                            print("2",lineNum) #TODO DELETE ME
                            return False

            else:  # if the justification is None, we will check if rule is none. if so than
                if line.rule is None:
                    if line.conclusion in self.statement.assumptions:
                        continue
                    else:  # if the conclusion of the line is not in the assumptions of the statement
                        print("3", lineNum) #TODO DELETE ME
                        return False
            # if self.lines[lineNum].just
            instance = self.instance_for_line(lineNum)
            rule = self.rules[line.rule]
            if not instance.is_instance_of(rule):
                print("4", lineNum) #TODO DELETE ME
                return False
        return self.lines[len(self.lines) - 1].conclusion == self.statement.conclusion


def instantiate(formula: Formula, instantiation_map: dict):
    """ Return a formula obtained from the given formula by simultaneously
        substituting, for each variable v that is a key of instantiation_map,
        each occurrence v with the formula instantiation_map[v] """
    # Task 5.2.1
    if is_variable(formula.root):
        return instantiation_map[formula.root]
    elif is_constant(formula.root):
        return formula.root
    elif is_unary(formula.root):
        first = instantiate(formula.first, instantiation_map)
        return Formula(NEGATE_OPERATOR, first)
    elif is_binary(formula.root):
        first = instantiate(formula.first, instantiation_map)
        second = instantiate(formula.second, instantiation_map)
        return Formula(formula.root, first, second)
    elif is_ternary(formula.root):
        first = instantiate(formula.first, instantiation_map)
        second = instantiate(formula.second, instantiation_map)
        third = instantiate(formula.third, instantiation_map)
        return Formula(formula.root, first, second, third)
    return formula


def prove_instance(proof: DeductiveProof, instance: InferenceRule):
    """ Return a proof of the given instance of the inference rule that proof
        proves, via the same inference rules used by proof """





    instantiation_map = {}
    if not instance.is_instance_of(proof.statement, instantiation_map):
        print(
            "there is a bug! you should've brought a valid proof. proof: {}, and instance: {}".format(proof, instance))
        return False
    lines = []
    for line in proof.lines:
        line_conclusion = instantiate(line.conclusion, instantiation_map)
        new_line = DeductiveProof.Line(line_conclusion, line.rule, line.justification)
        lines.append(new_line)
    return DeductiveProof(instance, proof.rules, lines)


def inline_proof(main_proof: DeductiveProof, lemma_proof: DeductiveProof) -> DeductiveProof:
    """ Return a proof of the inference rule that main_proof proves, via the
        inference rules used in main_proof except for the one proven by
        lemma_proof, as well as via the inference rules used in lemma_proof
        (with duplicates removed) """
    # Task 5.2.2
    index_to_switch = -1
    rules = []
    rules_dict = {}  # dictionary for all the rules that we want to add to the new proof
    main_rules_dict = {}  # dictionary of all the main proof rules
    lemma_rules_dict = {}  # dictionary of all the lemma proof rules
    proof_rule_index = 0
    rules_counter = 0
    index_to_switch, lemma_rules = create_rules(index_to_switch, lemma_proof,
                                                lemma_rules_dict, main_proof, main_rules_dict,
                                                proof_rule_index, rules, rules_counter,
                                                rules_dict)

    rules = rules + lemma_rules

    lines = []

    create_lines(index_to_switch, lemma_proof, lemma_rules_dict, lines, main_proof,
                 main_rules_dict, rules_dict)

    return DeductiveProof(main_proof.statement, rules, lines)


def create_rules(index_to_switch, lemma_proof, lemma_rules_dict, main_proof, main_rules_dict, proof_rule_index, rules,
                 rules_counter, rules_dict):
    """
    helper for inline_proof. its purpose is to make an order in the rules between the main_proof and the lemma,
    and create a list of rules to return
    :param index_to_switch:
    :param lemma_proof:
    :param lemma_rules_dict:
    :param main_proof:
    :param main_rules_dict:
    :param proof_rule_index:
    :param rules:
    :param rules_counter:
    :param rules_dict:
    :return:
    """
    # run on each line of the main proof
    for main_proof_rules_index in range(len(main_proof.rules)):  # run on all rules of the main proof by index
        # add each rule to a dictionary. the index is the key and the rule is the value
        main_rules_dict[rules_counter] = main_proof.rules[main_proof_rules_index]
        rules_counter += 1

        # if we find the rule that the lemma proofs = we save it's index and continue the loop
        if lemma_proof.statement.is_instance_of(main_proof.rules[main_proof_rules_index]):
            index_to_switch = main_proof_rules_index
            continue
        # else - we save the rule in a rule dictionary. where the rule is the key and its index is the value
        rules_dict[main_proof.rules[main_proof_rules_index].conclusion.infix()] = proof_rule_index
        proof_rule_index += 1

        rules.append(main_proof.rules[main_proof_rules_index])

    # create an instantiated lemma version
    lemma_rules = []
    rules_counter = 0
    for lemma_rule in lemma_proof.rules:  # run on all rules of the lemma
        # add the rule to the dictionary. the index is the key and the # rule is the value
        lemma_rules_dict[rules_counter] = lemma_rule

        rules_counter += 1

        is_duplicate = False

        # for each lemma_rule , we will check if it's an instance of the main_proof rules. if duplicated, don't add.
        for proof_rule in rules:
            if lemma_rule.is_instance_of(proof_rule):
                is_duplicate = True
        if not is_duplicate:
            lemma_rules.append(lemma_rule)

            rules_dict[lemma_rule.conclusion.infix()] = proof_rule_index
            proof_rule_index += 1
    return index_to_switch, lemma_rules


def create_lines(index_to_switch, lemma_proof, lemma_rules_dict, lines, main_proof,
                 main_rules_dict, rules_dict):
    """
    helper method for inline_proof. its purpose is to create a list of lines which we will return for the new proof.
    :param index_to_switch:
    :param lemma_proof:
    :param lemma_rules_dict:
    :param lines:
    :param main_proof:
    :param main_rules_dict:
    :param rules_dict:
    :return:
    """
    line_counter = 0
    old_lines_dict = {}
    # run on the number of lines in the main proof, by index
    for line_index in range(len(main_proof.lines)):

        main_line = main_proof.lines[line_index]  # variable for the main_proof current line
        if main_line.rule is None:  # if it's none, than keep it that way...
            old_lines_dict[line_index] = line_counter
            lines.append(DeductiveProof.Line(main_line.conclusion))
            line_counter += 1
        elif main_line.rule == index_to_switch:  # if the rule of the line matches the lemma we want to switch, go here

            inference_rule = main_proof.instance_for_line(line_index)
            new_proof = prove_instance(lemma_proof, inference_rule)

            lemma_line_counter = 0

            lemma_line_dictionary = {}
            for lemma_index in range(len(new_proof.lines)):  # for every line in the lemma's proof, by index
                lemma_line = new_proof.lines[lemma_index]  # variable for the new_lemma_proof current line

                if lemma_line.rule is None: # if the lemma rule is None - that means it's part of the assumptions. we
                                            #  will look at all the lines in the main_proof and match the right line
                    for i in range(len(lines)): # for every line in the new proof, by index
                        if lemma_line.conclusion == lines[i].conclusion:
                            lemma_line_dictionary[lemma_index] = i
                            continue
                    continue

                lemma_line_dictionary[lemma_index] = line_counter
                rule_num = rules_dict[lemma_rules_dict[lemma_line.rule].conclusion.infix()]

                justification_list = [lemma_line_dictionary[a] for a in lemma_line.justification]
                lines.append(DeductiveProof.Line(lemma_line.conclusion, rule_num, justification_list))

                line_counter += 1
                lemma_line_counter += 1
            old_lines_dict[line_index] = line_counter - 1

        else:
            old_lines_dict[line_index] = line_counter
            rule_num = rules_dict[main_rules_dict[main_line.rule].conclusion.infix()]

            justification_list = [old_lines_dict[a] for a in main_line.justification]
            lines.append(DeductiveProof.Line(main_line.conclusion, rule_num, justification_list))

            line_counter += 1
