# Bachelor's thesis - CNF from Dafny to F*

This project consists in porting the implementation of two algorithms (textbook and Tseitin's transformation) for finding the CNF of a propositional formula from Dafny to F*. The base implementation and the description of the algorithms can be found [here](https://github.com/iordacheviorel/cnf-dafny).

## Contents of the repository

The source files are:

1. *Utils.fst* - contains auxiliary lemmas and functions,
2. *FormulaT.fst* - contains the definition of the data type that represents a propositional formula, along with related lemmas and functions (definitions about validity, truth value, equivalence between two formulas etc),
3. *CnfFormula.fst* - contains lemmas and functions related to the representation of a formula in CNF (definitions about validity, truth value of a formula and its components, properties about appending two formulas etc),
4. *Cnf.fst* - contains the nine equivalence rules specific to the textbook algorithm and the recursive functions that use them to find the CNF of a given formula,
5. *TseitinCore.fst* - contains the definitions of the invariants used to prove the correctness and termination of the Tseitin algorithm,
6. *LemmasForClauses.{Not/Or/And/Implies/DImplies}Clauses.fst* - contains lemmas related to the clauses the algorithm adds for each logical connector,
7. *LemmasForClauses.fst* - includes the 5 modules from item 6,
8. *Tseitin.fst* - contains the functions *tseitin_cnf* and *tseitin* that are used to find the CNF of a given formula using the Tseitin algorithm,
9. *Main.fst* - contains an example of formula on which the two algorithms are tested,
10. *Makefile.include* - is used to include *fstar.exe* and the *Z3* solver, and
11. *Makefile* - is used for verifying and compiling the modules and for creating and running the executable.

## Compilation

The steps needed to install F* are described [here](https://github.com/FStarLang/FStar/blob/master/INSTALL.md#building-f-from-the-ocaml-sources).

The command used in the cygwin terminal (installed along with OCaml) to compile and verify the source files is:
```bash
make -C . all
```
Once the modules are verified, if only the *Main.fst* is being modified then the command that only verifies the main and uses the created *.checked* files in the folder *cache* is:
```bash
make -C . main
``` 