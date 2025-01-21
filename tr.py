from pysmt.shortcuts import Symbol, And, Or, Not, Equals, is_sat, Function, Implies, Iff, Or, EqualsOrIff, BOOL
from pysmt.typing import BOOL, FunctionType, INT
from pysmt.walkers import IdentityDagWalker
from pysmt.fnode import FNode


def get_boolean_skeleton(formula):
    # Dictionary to hold Boolean variables for each function application
    tr = {}
    tr_minus_one = {}
    counter = 1  # To create unique Boolean variables

    # Function to recursively traverse and replace uninterpreted functions
    def traverse(f):
        nonlocal counter  # Declare counter as nonlocal at the beginning
        if f.is_function_application():
            print("f: ", f)
            if f not in tr:
                # Create a new Boolean variable for each unique function application
                tr[f] = Symbol(f"f_{counter}", BOOL)
                tr_minus_one[tr[f]] = f
                counter += 1
            return tr[f]

        elif f.is_equals():
            if f not in tr:
                tr[f] = Symbol(f'x_{f}', BOOL)
                tr_minus_one[tr[f]] = f
            return tr[f]

        elif f.is_not():
            return Not(traverse(f.arg(0)))

        elif f.is_and():
            return And([traverse(f.arg(i)) for i in range(len(f.args()))])

        elif f.is_or():
            return Or([traverse(f.arg(i)) for i in range(len(f.args()))])

        elif f.is_implies():
            return Implies(traverse(f.arg(0)), traverse(f.arg(1)))

        elif f.is_iff():
            return Iff(traverse(f.arg(0)), traverse(f.arg(1)))

        else:
            return f  # Return the formula node as is if not a function application

    # Generate the Boolean skeleton of the formula
    skeleton_formula = traverse(formula)
    return skeleton_formula, tr, tr_minus_one

def cnf_to_dimacs(cnf_formula):
    # Map each Boolean variable to a unique integer
    var_to_int = {}
    int_to_var = {}
    next_var_id = 1

    def get_var_id(var):
        """Get the unique integer ID for a variable."""
        nonlocal next_var_id
        if var not in var_to_int:
            var_to_int[var] = next_var_id
            int_to_var[next_var_id] = var
            next_var_id += 1
        return var_to_int[var]

    # Flatten the CNF formula into a list of clauses
    if not cnf_formula.is_and():  # Ensure the formula is in CNF
        raise ValueError("Formula must be in Conjunctive Normal Form (CNF).")

    clauses = []
    for clause in cnf_formula.args():
        if clause.is_or():  # Each clause is a disjunction of literals
            literals = []
            for lit in clause.args():
                if lit.is_symbol():  # Positive literal
                    literals.append(get_var_id(lit))
                elif lit.is_not() and lit.arg(0).is_symbol():  # Negated literal
                    literals.append(-get_var_id(lit.arg(0)))
                else:
                    raise ValueError(f"Unsupported literal format: {lit}")
            clauses.append(literals)
        elif clause.is_symbol():  # Single literal clause
            clauses.append([get_var_id(clause)])
        elif clause.is_not() and clause.arg(0).is_symbol():  # Negated single literal clause
            clauses.append([-get_var_id(clause.arg(0))])
        else:
            raise ValueError(f"Unsupported clause format: {clause}")

    num_vars = len(var_to_int)
    return clauses, var_to_int, int_to_var

def substitute_model(model, int_to_var):
    literals = []
    for literal in model:
        variable = int_to_var[abs(literal)]  # Get the variable from the map
        value = variable if literal > 0 else Not(variable)  # Determine the value based on the sign of the literal
        literals.append(value)

    # Return the conjunction of all literals in the model
    return literals

def substitute_model_minus_one(model, var_to_int):
    literals = []
    for literal in model:
        if literal.is_not():
            variable = var_to_int[literal.arg(0)]
            literals.append(-variable)
        else:
            variable = var_to_int[literal]  # Get the variable from the map
            literals.append(variable)

    # Return the conjunction of all literals in the model
    return literals

def substitute_tr_minus_one(model, tr_minus_one):
    literals = []
    for literal in model:
        if literal in tr_minus_one:
            variable = tr_minus_one[literal]  # Get the variable from the map
            literals.append(variable)
        elif literal.is_not() and literal.arg(0) in tr_minus_one:
            variable = tr_minus_one[literal.arg(0)]
            literals.append(Not(variable))

    # Return the conjunction of all literals in the model
    return literals

def not_phi_model(model):
    literals = []
    for literal in model:
        if literal.is_not():
            literals.append(literal.arg(0))
        else:
            literals.append(Not(literal))


    # Return the conjunction of all literals in the model
    return literals

# flatenning
def flattening(cube):
    # cube = [formula]
    new_cube = []
    while cube != new_cube:
        new_cube = cube.copy()

        cube = equal_rule(cube)
        if cube != new_cube:
            continue

        cube = not_s_rule(cube)
        if cube != new_cube:
            continue

        cube = not_t_rule(cube)
        if cube != new_cube:
            continue

        cube = function_rule(cube)
        if cube != new_cube:
            continue

        cube = predicat_rule(cube)
        if cube != new_cube:
            continue

        cube = not_predicat_rule(cube)
        if cube != new_cube:
            continue
        return And(cube)


def equal_rule(cube):
    for lit in cube:
        if lit.is_equals():
            left, right = lit.args()
            if not left.is_symbol():
                cube.remove(lit)
                new_symbol = Symbol(f"x_{left}", left.get_type())
                cube.extend([EqualsOrIff(new_symbol, right), EqualsOrIff(new_symbol, left)])
                return cube
    return cube

def not_s_rule(cube):
    for lit in cube:
        if lit.is_not() and lit.args()[0].is_equals():
            left, right = lit.args()[0].args()
            if not left.is_symbol():
                cube.remove(lit)
                new_symbol = Symbol(f"x_{left}", left.get_type())
                cube.extend([Not(EqualsOrIff(new_symbol, right)), EqualsOrIff(new_symbol, left)])
                return cube
    return cube

def not_t_rule(cube):
    for lit in cube:
        if lit.is_not() and lit.args()[0].is_equals():
            left, right = lit.args()[0].args()
            if left.is_symbol() and not right.is_symbol():
                cube.remove(lit)
                new_symbol = Symbol(f"x_{right}", right.get_type())
                cube.extend([Not(EqualsOrIff(left, new_symbol)), EqualsOrIff(new_symbol, right)])
                return cube
    return cube

def function_rule(cube):
    for lit in cube:
        if lit.is_equals():
            left, right = lit.args()
            if left.is_symbol() and right.is_function_application():
                non_symbol = next((arg for arg in right.args() if not arg.is_symbol()), [])
                if non_symbol != []:
                    cube.remove(lit)
                    new_symbol = Symbol(f"x_{non_symbol}", non_symbol.get_type())
                    new_args = [new_symbol if arg == non_symbol else arg for arg in right.args()]
                    new_func = Function(right.function_name(), new_args)
                    cube.extend([EqualsOrIff(left, new_func), EqualsOrIff(new_symbol, non_symbol)])
                    return cube
    return cube

def predicat_rule(cube):
    for lit in cube:
        if lit.is_function_application() and lit.get_type() == BOOL:
            non_symbol = next((arg for arg in lit.args() if not arg.is_symbol()), [])
            if non_symbol != []:
                cube.remove(lit)
                new_symbol = Symbol(f"x_{non_symbol}", non_symbol.get_type())
                new_args = [new_symbol if arg == non_symbol else arg for arg in lit.args()]
                new_predicat = Function(lit.function_name(), new_args)
                cube.extend([new_predicat, EqualsOrIff(new_symbol, non_symbol)])
                return cube
    return cube

def not_predicat_rule(cube):
    for lit in cube:
        if lit.is_not() and lit.args()[0].is_function_application() and lit.args()[0].get_type() == BOOL:
            non_symbol = next((arg for arg in lit.args()[0].args() if not arg.is_symbol()), [])
            if non_symbol != []:
                cube.remove(lit)
                new_symbol = Symbol(f"x_{non_symbol}", non_symbol.get_type())
                new_args = [new_symbol if arg == non_symbol else arg for arg in lit.args()[0].args()]
                new_predicat = Function(lit.args()[0].function_name(), new_args)
                cube.extend([Not(new_predicat), EqualsOrIff(new_symbol, non_symbol)])
                return cube
    return cube



# Example usage
if __name__ == "__main__":

    # Define some symbols and an uninterpreted function
    f_type = FunctionType(BOOL, [BOOL])
    x = Symbol("x", BOOL)
    y = Symbol("y", BOOL)
    f = Symbol("f", f_type)

    # Create a formula with uninterpreted function applications
    formula = And(Function(f, [Function(f, [y])]), Or(y, Or(Not(Function(f, [x])), x)))

    # Get the Boolean skeleton of the formula
    skeleton, tr, tr_minus_one = get_boolean_skeleton(formula)

    # Print the results
    print("Original Formula:", formula)
    print("Boolean Skeleton:", skeleton)
    print("tr:", tr)
    print("tr_minus_one:", tr_minus_one)

    trans = translate_boolean_vars(skeleton, tr_minus_one)
    print("trans:", trans)

