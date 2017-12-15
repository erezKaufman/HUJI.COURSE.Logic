""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/test_ex8.py """

from predicates.syntax_test import *
from predicates.functions_test import *

def test_task1(debug=False):
    test_term_functions(debug)
    test_formula_functions(debug)
    test_relations(debug)

def test_task2(debug=False):
    test_replace_functions_with_relations_in_model(debug)

def test_task3(debug=False):
    test_replace_relations_with_functions_in_model(debug)

def test_task4(debug=False):
    test_compile_term(debug)

def test_task5(debug=False):
    test_replace_functions_with_relations_in_formula(debug)

def test_task6(debug=False):
    test_replace_functions_with_relations_in_formulae(debug)

def test_task7(debug=False):
    test_replace_equality_with_SAME(debug)

def test_task8(debug=False):
    test_add_SAME_as_equality(debug)

def test_task9(debug=False):
    test_make_equality_as_SAME(debug)

# test_task1(True)
# test_task2(True)
# test_task3(True)
# test_task4(True)
# test_task5(True)
# test_task6(True)
test_task7(True)
# test_task8(True)
# test_task9(True)

# 88 File "staff_code/ex8_presubmission.py", line 44, in <module>
# 89 globals()[test_name](True)
# 90 File "staff_code/ex8_presubmission.py", line 32, in test_task7
# 91 test_replace_equality_with_SAME(debug)
# 92 File "/tmp/bodek.1U2eOV/logic/automatic_feedback_for_ex8/bar371/presubmission/testdir/staff_code/predicates/functions_test.py", line 217, in test_replace_equality_with_SAME
# 93 ’is’ if staff_is_model_of(model, new_formulae) else ’is not’,
# 94 File "/tmp/bodek.1U2eOV/logic/automatic_feedback_for_ex8/bar371/presubmission/testdir/staff_code/predicates/staff_sol.py", line 19, in staff_is_model_of
# 95 formula = Formula(’A’, free_variable, formula)
# 96 File "/tmp/bodek.1U2eOV/logic/automatic_feedback_for_ex8/bar371/presubmission/testdir/staff_code/predicates/syntax.py", line 248, in __init__
# 97 assert is_variable(first) and type(second) is Formula
# 98 File "/tmp/bodek.1U2eOV/logic/automatic_feedback_for_ex8/bar371/presubmission/testdir/staff_code/predicates/syntax.py", line 39, in is_variable
# 99 return s[0] >= ’u’ and s[0] <= ’z’ and s.isalnum()
# 100 TypeError: ’Term’ object does not support indexing