#!/bin/bash

python ex2_tests_eliav.py
cd results

ECHO  "Check Task1"
if FC  task1 task1_temp; then
	ECHO "Passed Task1"
else
	ECHO "Failed Task1"
fi

ECHO "Check Task2"
if FC task2 task2_temp; then
	ECHO "Passed Task2"
else
	ECHO "Failed Task2"
fi

ECHO "Check Task3"
if FC task3 task3_temp; then
	ECHO "Passed Task3"
else
	ECHO "Failed Task3"
fi

ECHO "Check Task4"
if FC task4 task4_temp; then
	ECHO "Passed Task4"
else
	ECHO "Failed Task4"
fi

ECHO "Check Task5"
if FC task5 task5_temp; then
	ECHO "Passed Task5"
else
	ECHO "Failed Task5"
fi

ECHO "Check Task6"
if FC task6 task6_temp; then
	ECHO "Passed Task6"
else
	ECHO "Failed Task6"
fi

ECHO "Check Task7"
if FC task7 task7_temp; then
	ECHO "Passed Task7"
else
	ECHO "Failed Task7"
fi

rm -f *_temp