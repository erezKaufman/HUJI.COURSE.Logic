""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/prover.py """

from predicates.proofs import *


class Prover:
    """ A class for gradually constructing a first-order Proof for a given
        conclusion, from given assumptions as well as from the six AXIOMS
        Universal Instantiation (UI), Existential Introduction (EI), Universal
        Simplification (US), Existential Simplification (ES), Reflexivity (RX),
        and Meaning of Equality (ME) """
    UI = Schema('(Ax[R(x)]->R(c))', {'R', 'x', 'c'}) #Ax[plus(x,y)=plus(y,x)] ->plus(c,y)=plus(y,c)
    # Ax[R(X)]->R(C) | (Ax[0=plus(minus(z1,z1))]->0=plus(minus(minus(x),minus(x))))
    EI = Schema('(R(c)->Ex[R(x)])', {'R', 'x', 'c'})
    US = Schema('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'x', 'Q', 'R'})
    ES = Schema('((Ax[(R(x)->Q())]&Ex[R(x)])->Q())', {'x', 'Q', 'R'})
    RX = Schema('c=c', {'c'})
    ME = Schema('(c=d->(R(c)->R(d)))', {'c', 'd', 'R'})
    AXIOMS = [UI, EI, US, ES, RX, ME]

    def __init__(self, assumptions, conclusion, print_as_proof_forms=False):
        """ Constructs a new Prover. Each element in assumptions may either be
            a Schema or a string, with the latter interpreted as a schema with
            no templates whose unique instance is the given string. Any
            element in assumptions that is already in Prover.AXIOMS is ignored
            as an element of assumptions, to avoid duplication. conclusion
            is the conclusion or its string representation. The Boolean flag
            print_as_proof_forms specifies whether the proof being constructed
            is to be printed in real time as it is being constructed """
        self.proof = Proof(Prover.AXIOMS +
                           [Schema(assumption)
                            if type(assumption) is str else assumption
                            for assumption in assumptions
                            if assumption not in Prover.AXIOMS],
                           Formula.parse(conclusion)
                           if type(conclusion) is str else conclusion, [])
        self.print_as_proof_forms = print_as_proof_forms
        if self.print_as_proof_forms:
            print("Starting Proof")
            print("Assumptions: AXIOMS +", assumptions)
            print("Conclusion:", self.proof.conclusion)

    def _add_line(self, statement, justification):
        """ Append to the proof being constructed the validly justified line
            whose formula is statement and whose justification is given. The
            validity of the added line is asserted, and its number in this
            proof is returned """
        assert type(statement) is Formula or type(statement) is str
        if type(statement) is str:
            statement = Formula.parse(statement)
        line = len(self.proof.lines)
        self.proof.lines.append(Proof.Line(statement, justification))
        assert self.proof.verify_justification(line)
        if self.print_as_proof_forms:
            print(str(line) + ")", statement)
        return line

    def add_instantiated_assumption(self, instance, schema, instantiation_map):
        """ Append to the proof being constructed a validly justified line
            whose formula is instance, which is the result of an instantiation
            via instantiation_map of the given schema, which must be one of the
            assumptions/axioms of this proof. The number of the added line in
            this proof is returned """
        assert type(instance) is Formula or type(instance) is str
        assert type(schema) is Schema
        return self._add_line(instance,
                              ('A', self.proof.assumptions.index(schema),
                               instantiation_map))

    def add_assumption(self, assumption):
        """ Append to the proof being constructed a validly justified line
            whose formula is assumption, which is the (unique) instance of a
            schema with no templates that is one of the assumptions/axioms of
            this proof. The number of the added line in this proof is returned
        """
        assert type(assumption) is Formula or type(assumption) is str
        return self.add_instantiated_assumption(
            assumption, Schema(str(assumption)), {})

    def add_tautology(self, tautology):
        """ Append to the proof being constructed a validly justified line
            whose formula is tautology, which is a tautology. The number of the
            added line in this proof is returned """
        assert type(tautology) is Formula or type(tautology) is str
        return self._add_line(tautology, ('T',))

    def add_mp(self, consequent, antecedent_line, conditional_line):
        """ Append to the proof being constructed a validly justified line
            whose formula is consequent, and which is a return of applying
            Modus Ponens over lines atecedent_line and conditional_line in this
            proof. The number of the added line in this proof is returned """
        assert type(consequent) is Formula or type(consequent) is str
        return self._add_line(consequent,
                              ('MP', antecedent_line, conditional_line))

    def add_ug(self, quantified, unquantified_line):
        """ Append to the proof being constructed a validly justified line
            whose formula is quantified, and which is a return of universal
            generalization over line unquantified_line in this proof. The
            number of the added line in this proof is returned """
        assert type(quantified) is Formula or type(quantified) is str
        return self._add_line(quantified, ('UG', unquantified_line))

    def add_proof(self, conclusion, proof):
        """ Append to the proof being constructed a whole copy of the
            given proof, where the formula of the last line is conclusion.
            The given proof must have the same list of assumptions, and
            this method takes care of the required line-shift in the
            justifications.  The number of the (new) line in this proof
            containing conclusion is returned """
        assert proof.assumptions == self.proof.assumptions
        line_shift = len(self.proof.lines)
        for line in proof.lines:
            if line.justification[0] == 'A' or line.justification[0] == 'T':
                self._add_line(line.formula, line.justification)
            if line.justification[0] == 'MP':
                self.add_mp(line.formula, line.justification[1] + line_shift,
                            line.justification[2] + line_shift)
            if line.justification[0] == 'UG':
                self.add_ug(line.formula, line.justification[1] + line_shift)
        line_number = len(self.proof.lines) - 1
        assert str(self.proof.lines[line_number].formula) == str(conclusion)
        return line_number

    def add_universal_instantiation(self, instantiation: str, line_number: int, term: str) -> int:
        """
        Append a sequence of validly justified lines to the proof being
        constructed, where the formula of the last line is statement, which
        is an instantiation of the formula in line line_number in this
        proof, where the instantiation is to the universally
        quantified variable appearing at the beginning of the formula in
        the given line number. Example: if line line_number has the formula
        'Ay[Az[f(x,y)=g(z,y)]]', then when calling this method with the
        term 'h(w)', the instantiation should be
        'Az[f(x,h(w))=g(z,h(w))]'. The number of the (new) line in this
        proof containing instantiation is returned
        """
        # Task 10.1

        # I receive a line number, I need to reach it and take the formula there. Then I need to  set the variable in
        #  the quantifier to be as 'x', the Formula inside of the quantifier to be as 'R' and the constant after the
        # get the formula form of the current line, and check it's a quantifier
        line_formula = self.proof.lines[line_number].formula
        assert is_quantifier(line_formula.root)
        # create an instantiation map and add to it the instantiated values
        instantiation_map = {}
        x_var = str(line_formula.variable)  # the x instantiated value will be the variable of the quantifier
        r_var = str(line_formula.predicate)  # the R instantiated value will be the predicate of the quantifier
        term_obj = term  # the c instantiated value will be the whole term

        instantiation_map['R(' + x_var + ')'] = r_var
        instantiation_map['x'] = x_var
        instantiation_map['c'] = term_obj

        ui_formula = self.AXIOMS[0].instantiate(instantiation_map)
        ui_line_num = self.add_instantiated_assumption(ui_formula, Prover.UI, instantiation_map)

        return self.add_mp(instantiation, line_number, ui_line_num)

    def add_tautological_inference(self, conclusion, line_numbers):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is conclusion,
            which is a tautological inference of the formulae in the lines in
            this proof whose numbers are given in the list line_numbers. The
            number of the (new) line in this proof containing conclusion is
            returned """
        # Task 10.2
        formula = Formula.parse(conclusion)
        for i in range(len(line_numbers) - 1, -1, -1):
            formula = Formula('->', self.proof.lines[line_numbers[i]].formula, formula)
        print(formula)
        last_line_number = self.add_tautology(formula)
        for j in range(len(line_numbers)):
            last_line_number = self.add_mp(formula.second, line_numbers[j], last_line_number)
            formula = formula.second
        return last_line_number

    def add_existential_derivation(self, statement, line1, line2):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is statement.
            The formula in line line1 must be of the form 'Ex[cond(x)]' (for
            some variable x), and the formula in line line2 must be of the form
            'cond(x)->statement' (where x is not free is statement). The number
            of the (new) line in this proof containing statement is returned """
        # Task 10.3

        formula1 = self.proof.lines[line1].formula
        formula2 = self.proof.lines[line2].formula
        assert is_quantifier(formula1.root)
        assert formula2.root == '->'

        # create quantified formula 2:
        f1_var = formula1.variable
        quantified_form2 = Formula('A', f1_var, formula2)
        quantified_form2_line = self.add_ug(str(quantified_form2), line2)
        # create es formula
        part_1_es = Formula('&', self.proof.lines[quantified_form2_line].formula, formula1)
        es_formula = Formula('->', part_1_es, formula2.second)
        # finished es formula
        # create new instantiation map for ES
        sub = formula1.predicate.substitute({f1_var: Term('v')})
        instantiation_map = {'x': f1_var, 'R(v)': str(sub), 'Q()': str(formula2.second)}
        es_line = self.add_instantiated_assumption(es_formula, Prover.ES, instantiation_map)
        return self.add_tautological_inference(statement, [line1, quantified_form2_line, es_line])

    def add_flipped_equality(self, flipped, line_number):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is flipped,
            which is an equality of the form 'c=d' (for some terms c, d) where
            the formula in line line_numer in this proof is 'd=c'. The number
            of the (new) line in this proof containing flipped is returned """
        # Task 10.6
        unflipped_formula = self.proof.lines[line_number].formula
        first_term = str(unflipped_formula.first)
        second_term = str(unflipped_formula.second)
        me_instantiation_map = {'c': first_term, 'd': second_term, 'R(v)': 'v=' + first_term}
        rx_instantiation_map = {'c': first_term}
        me_line_number = self.add_instantiated_assumption(Prover.ME.instantiate(me_instantiation_map), Prover.ME,
                                                          me_instantiation_map)
        rx_line_number = self.add_instantiated_assumption(Prover.RX.instantiate(rx_instantiation_map), Prover.RX,
                                                          rx_instantiation_map)
        return self.add_tautological_inference(flipped, [line_number, me_line_number, rx_line_number])

    def add_free_instantiation(self, instantiation, line_number,
                               substitution_map):

        def compile_term_helper(term_helper: Term, z_list_helper):
            """

            :param term_helper: the term to process
            :param z_list_helper:  our list of formula's to update
            """
            if is_constant(term_helper.root) or is_variable(term_helper.root):
                var = next(fresh_variable_name_generator)
                zs_dict[term_helper] = Term(var)
                return

            for arg in term_helper.arguments:
                compile_term_helper(arg, z_list_helper)

            if is_function(term_helper.root):
                var = next(fresh_variable_name_generator)
                new_args = []  # holds the new args for this trem, if one of the args should be z_i append that
                for arg in term_helper.arguments:  # iterate over all term_helper's args
                    if is_function(arg.root):
                        if arg in zs_dict.keys():  # it's possible we already added this var , if so
                            new_args.append(zs_dict[arg])  # just append it!
                    else:
                        new_args.append(arg)  # this is a new arg for a var, append it

                result = Formula('=', Term(var), Term(term_helper.root, new_args))
                z_list_helper.append(result)
                zs_dict[term_helper] = Term(var)

        def sub_single_var(line, z_value, sub_value):
            # phi(x)
            #
            # 1.
            # Ax[phi(x)][UG, 0]
            #
            # 2.
            # Ax[phi(x)]->phi(c)[UI]

            # 3.
            # phi(c)[MP, 1, 2]
            # step_1 =
            pass

        def make_z_lines(formula, z_list):
                if is_unary(formula.root):  # call recursivly with first
                    make_z_lines(formula.first, z_list)

                # treat of all these the same way - either make a new z or list an old one
                elif is_equality(formula.root):
                    compile_term_helper(formula.first, z_list)
                    compile_term_helper(formula.second, z_list)

                elif is_relation(formula.root):
                    for term in formula.arguments:
                        compile_term_helper(term, z_list)

                elif is_quantifier(formula.root):
                    make_z_lines(formula.predicate, z_list)

                elif is_binary(formula.root):
                    make_z_lines(formula.first, z_list)
                    make_z_lines(formula.second, z_list)


        """ Append a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is statement, which
            is an instantiation of the formula in line line_number in this
            proof, where the instantiation is simultaneously to the free
            variables appearing as keys in the substitution map. Example: if
            line line_number has the formula 'Az[f(x,y)=g(z,y)]', then when
            calling this method with the substitution map {'y':'h(w)'}, the
            instantiation should be 'Az[f(x,h(w))=g(z,h(w))]'. The number of the
            (new) line in this proof containing instantiation is returned """
        # Task 10.7
        current_formula = self.proof.lines[line_number].formula  # plus(x,y)=plus(y,x)
        # create the z dictionary
        z_dict = {}
        for key in substitution_map:
            z_dict[key] = next(fresh_variable_name_generator)
        # let's say I receive a dictionary of variables as keys and zs as values. I will substitute each time it
        # shows with zs, and then run in loop to find each z and substitute with value in substitution_map
        for key, value in z_dict.items(): # {x; z1, y: z2}
            quantified_current_formula = Formula('A', key, current_formula)
            current_formula = current_formula.substitute({key: Term(value)}) # plus(z1,y)=plus(y,z1)
            cur_ug_line = self.add_ug(quantified_current_formula, line_number)
            line_number = self.add_universal_instantiation(current_formula,cur_ug_line,value)

        # run on all items in the z dictionary, and for each occurrence - switch the z with the proper term
        for key, value in z_dict.items():
            quantified_current_formula = Formula('A',value,current_formula)
            current_formula = current_formula.substitute({value: Term.parse(substitution_map[key])})
            cur_ug_line = self.add_ug(quantified_current_formula, line_number)
            line_number = self.add_universal_instantiation(current_formula,cur_ug_line,substitution_map[key])

        return line_number


        zs_dict = {}
        z_list = []
        f = self.proof.lines[line_number].formula
        make_z_lines(f, z_list)
        print(zs_dict)




        for key in zs_dict.keys():
            sub_single_var()




    def add_substituted_equality(self, substituted, line_number,
                                 term_with_free_v):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is substituted,
            which is an equality of two terms, each of which is derived by
            substituting a term for the variable v in term_with_free_v. The
            two terms to be substituted for v are the two sides of the equality
            that is the formula in line line_number in this proof. Example: if
            line line_number has the formula 'g(x)=h(y)' and term_with_free_v
            is 'v+7', then substituted should be 'g(x)+7=h(y)+7'. The number of
            the (new) line in this proof containing substituted is returned """
        # Task 10.8

    def _add_chained_two_equalities(self, line1, line2):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is an equality of
            the form 'c=d' (for some terms c, d) where the formulae in lines
            line1 and line2 in this proof are respectively 'c=a' and 'a=d' (for
            some term a). Example: if Line 7 holds 'a=b', and Line 3 holds
            'b=f(b)', then if line1=7 and line2=3, then the formula of the last
            line added will be the chained equality 'a=f(b)'. The number of the
            (new) line in this proof containing the chained equality is
            returned """
        # Task 10.9.1

    def add_chained_equality(self, chained, line_numbers):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is chained, which
            is an equality of the form 'c=d' (for some terms c, d) where the
            formulae in the lines in this proof whose numbers are given in the
            list line_numbers are of the form (in order) 'c=a1', 'a1=a2', ...,
            'an=d' (for some n and some terms a1,a2,...,an). Example: if Line 7
            holds 'a=b', Line 3 holds 'b=f(b)' and Line 9 holds 'f(b)=0', then
            if line_numbers=[7,3,9], then chained should be 'a=0'. The number of
            the (new) line in this proof containing substituted is returned """
        # Task 10.9.2
