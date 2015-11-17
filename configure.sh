#!/bin/sh

echo "Generating Makefile out of _CoqProject file"
coq_makefile -f _CoqProject -o Makefile

echo "Generating .merlin file to enable merlin"

echo "#This .merlin file is generated automatically by the configure script." > src/.merlin
echo "" >> src/.merlin
echo "FLG -rectypes" >> src/.merlin
echo "" >> src/.merlin
echo "S $(coqc -where)/**" >> src/.merlin
echo "B $(coqc -where)/**" >> src/.merlin
