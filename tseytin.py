from pysmt.shortcuts import Symbol, And, Not, Or, Implies, Iff
from pysmt.typing import BOOL


def tseitin_transformation(formula):
    # Dictionary to hold new variables for subformulas
    subformula_vars = {}
    clauses = []

    def tseitin_subformula(f):
        if f.is_symbol():  #  If it's a symbol, return it
            return f

        if f in subformula_vars:  # If we've already processed this formula, reuse its variable
            return subformula_vars[f]

        # Create a new variable for the current formula
        new_var = Symbol("p{}".format(len(subformula_vars) + 1), BOOL)
        subformula_vars[f] = new_var

        # Process the formula based on its type
        if f.is_not():
            sub_var = tseitin_subformula(f.arg(0))
            clauses.append(Or(Not(new_var), Not(sub_var)))
            clauses.append(Or(new_var, sub_var))
        elif f.is_and():
            left = tseitin_subformula(f.arg(0))
            right = tseitin_subformula(f.arg(1))
            # new_var <-> (left AND right)
            clauses.append(Or(Not(new_var), left))
            clauses.append(Or(Not(new_var), right))
            clauses.append(Or(new_var, Not(left), Not(right)))
        elif f.is_or():
            left = tseitin_subformula(f.arg(0))
            right = tseitin_subformula(f.arg(1))
            # new_var <-> (left OR right)
            clauses.append(Or(Not(new_var), left, right))
            clauses.append(Or(new_var, Not(left)))
            clauses.append(Or(new_var, Not(right)))
        elif f.is_iff():
            left = tseitin_subformula(f.arg(0))
            right = tseitin_subformula(f.arg(1))
            # new_var <-> (left <-> right)
            clauses.append(Or(Not(new_var), Not(left), right))
            clauses.append(Or(Not(new_var), left, Not(right)))
            clauses.append(Or(new_var, Not(left), Not(right)))
            clauses.append(Or(new_var, left, right))
        elif f.is_implies():
            left = tseitin_subformula(f.arg(0))
            right = tseitin_subformula(f.arg(1))
            # new_var <-> (left -> right)
            clauses.append(Or(Not(new_var), Not(left), right))
            clauses.append(Or(new_var, left))
            clauses.append(Or(new_var, Not(right)))
        else:
            raise ValueError("Unsupported operator: {}".format(f))

        return new_var

    # Add the root formula as the final clause
    root_var = tseitin_subformula(formula)
    clauses.append(Or(root_var))

    # Return the CNF formula as a conjunction of clauses
    return And(clauses)



# Example usage:
if __name__ == "__main__":
    # Define symbols
    A = Symbol("A", BOOL)
    B = Symbol("B", BOOL)
    C = Symbol("C", BOOL)
    D = Symbol("D", BOOL)
    E = Symbol("E", BOOL)
    F = Symbol("F", BOOL)
    G = Symbol("G", BOOL)
    H = Symbol("H", BOOL)

    # Example
    formula1 = And(Or(And(A, B), And(C, Not(D))), Or(E, Not(F)), Implies(G, H))
    formula2 = Implies(Implies(A, B), Implies(Not(B), C))
    formula3 = And(Iff(A, B), Iff(Not(C), D))
    formula4 = And(Or(A, B), Not(And(A, B)))

    #our
    formula5 = Or(And(A, Not(B)), And(C, Or(D, Not(A))))
    formula6 = Or(Implies(A, B), Iff(C, Not(D)))

    # Apply Tseitin transformation
    cnf_formula = tseitin_transformation(formula6)
    print("formula:", formula6)
    print("CNF formula:", cnf_formula)
