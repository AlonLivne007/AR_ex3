import sys

from tr import cnf_to_dimacs
from tseytin_origin import tseitin_transformation
from pysmt.shortcuts import Symbol, And, Equals, Or, Not, BOOL, Iff, TRUE, FALSE
from pysmt.smtlib.parser import SmtLibParser
from cdcl_solver1_vsids import cdcl_solve




def bit_blasting(formula):
    """
    Perform bit-blasting on the given formula in bit-vector arithmetic.
    Assumes all bit-vectors have a width of 4.
    """
    # Map to hold the Boolean variables for each bit
    boolean_vars = {}

    def create_boolean_variables(term):
        """
        Create 4 Boolean variables for the term.
        """
        if term not in boolean_vars:
            boolean_vars[term] = [Symbol(f"{str(term)}_{i}", BOOL) for i in range(4)]
        return boolean_vars[term]

    def bitwise_constraints(op, a_bits, b_bits, result_bits):
        """
        Generate bitwise constraints for the given operation (AND, OR, XOR, etc.).
        """
        constraints = []
        for i in range(4):  # Fixed width of 4 bits
            if op == "and":
                constraints.append(Iff(result_bits[i], And(a_bits[i], b_bits[i])))
            elif op == "or":
                constraints.append(Iff(result_bits[i], Or(a_bits[i], b_bits[i])))
            elif op == "eq":
                constraints.append(Iff(result_bits[i], Iff(a_bits[i], b_bits[i])))
        return constraints

    def handle_formula(formula):
        """
        Recursively handle the formula to generate bit-blasted constraints.
        """
        if formula.is_symbol():
            # Base case: It's a variable (bit-vector or Boolean)
            return create_boolean_variables(formula), []

        elif formula.is_and():
            # Handle conjunction (AND)
            all_constraints = []
            for subformula in formula.args():
                _, sub_constraints = handle_formula(subformula)
                all_constraints.extend(sub_constraints)
            return None, all_constraints  # AND combines constraints only, no new variables

        elif formula.is_or():
            # Handle disjunction (OR)
            all_constraints = []
            for subformula in formula.args():
                _, sub_constraints = handle_formula(subformula)
                all_constraints.extend(sub_constraints)
            return None, all_constraints  # OR combines constraints only, no new variables

        elif formula.is_bv_and() or formula.is_bv_or():
            # Recursive case: Bitwise operations
            a_bits, a_constraints = handle_formula(formula.arg(0))
            b_bits, b_constraints = handle_formula(formula.arg(1))
            result_bits = create_boolean_variables(formula)
            op = "and" if formula.is_bv_and() else "or"
            constraints = bitwise_constraints(op, a_bits, b_bits, result_bits)
            # Combine constraints from recursive calls with the current operation's constraints
            return result_bits, a_constraints + b_constraints + constraints

        elif formula.is_equals():
            # Recursive case: Equality
            a_bits, a_constraints = handle_formula(formula.arg(0))
            b_bits, b_constraints = handle_formula(formula.arg(1))
            result_bits = create_boolean_variables(formula)
            constraints = bitwise_constraints("eq", a_bits, b_bits, result_bits)
            # Combine constraints from recursive calls with the current operation's constraints
            return result_bits, a_constraints + b_constraints + constraints


        elif formula.is_constant():
            # Base case: Constant bit-vector
            constant_value = formula.constant_value()  # Extract the numeric value of the constant
            result_bits = create_boolean_variables(
                formula)  # Create Boolean variables for the constant
            constraints = []

            for i in range(4):  # Iterate over all 4 bits (fixed width)
                # Extract the i-th bit of the constant (0 or 1)
                bit_value = (constant_value >> i) & 1
                if bit_value == 1:
                    # Represent True as (p | ~p) using a dummy variable
                    dummy_var = Symbol(f"dummy_true_{i}", BOOL)
                    constraints.append(
                        Or(dummy_var, Not(dummy_var)))  # Add (p | ~p)
                    constraints.append(Iff(result_bits[i],
                                           dummy_var))  # result_bits[i] <=> dummy_var
                else:
                    # Represent False as (p & ~p) using a dummy variable
                    dummy_var = Symbol(f"dummy_false_{i}", BOOL)
                    constraints.append(
                        And(dummy_var, Not(dummy_var)))  # Add (p & ~p)
                    constraints.append(Iff(result_bits[i],
                                           dummy_var))  # result_bits[i] <=> dummy_var

            return result_bits, constraints

        else:
            raise NotImplementedError(f"Unsupported operation: {formula}")

    # Start processing the formula
    result_bits, constraints = handle_formula(formula)
    return And(constraints)







def flatten_bv(cube):
    return 0



def bv_solver(formula):
    cnf, var_to_int, int_to_var = cnf_to_dimacs(tseitin_transformation(bit_blasting(formula)))
    return cdcl_solve(cnf)


filepath = sys.argv[1]
parser = SmtLibParser()
with open(filepath, "r") as f:
    script = parser.get_script(f)
    formula = script.get_last_formula()
    print(formula)
    print (bv_solver(formula))  # Outputs the parsed formula
