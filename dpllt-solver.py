# importing system module for reading files
import sys

from bv_solver import bv_solver
from cdcl_vsids import CDCLSolver
from tr import get_boolean_skeleton, cnf_to_dimacs, substitute_model, substitute_tr_minus_one, not_phi_model, \
                substitute_model_minus_one
from tseytin import tseitin_transformation

# import classes for parsing smt2 files
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO

def dpll_t(formula):
    # Step 1: Generate the Boolean skeleton of the formula in CNF.
    skelton_boolean, tr, tr_minus_one = get_boolean_skeleton(formula)
    tseitin = tseitin_transformation(skelton_boolean)
    cnf, var_to_int, int_to_var = cnf_to_dimacs(tseitin)
    solver = CDCLSolver()
    while True:
        # Step 2: Run a SAT solver on the Boolean skeleton to find a propositional model.
        model = solver.cdcl_solve(cnf)

        # If the SAT solver returns unsat, it means the Boolean skeleton is unsatisfiable.
        # In this case, the entire formula is unsatisfiable, so we return "unsat".
        if model is None:
            return "unsat";

        # Step 3: Check if the propositional model also satisfies the theory part of the formula.
        model = substitute_model(model, int_to_var)
        model = substitute_tr_minus_one(model, tr_minus_one)
        uf_model = bv_solver(model)
        # If the theory solver confirms the model is valid under the theory, the formula is satisfiable.
        # Return "sat" to indicate that a satisfying assignment was found.
        if uf_model is not None:
            return "sat";

        # Step 4: Refine the formula by adding a clause that excludes negates  the current model.
        # This forces the SAT solver to find a different propositional model in the next iteration.
        not_model = not_phi_model(model)
        not_model = substitute_tr_minus_one(not_model, tr)
        not_model = substitute_model_minus_one(not_model, var_to_int)
        cnf = cnf + [not_model]


# read path from input
path = sys.argv[1]
with open(path, "r") as f:
    smtlib = f.read()

    # parse the smtlib file and get a formula
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(smtlib))
    formula = script.get_last_formula()

    print("\nOriginal Formula:", formula)

    print("sat" if dpll_t(formula) == "sat" else "unsat")