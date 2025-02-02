from pysmt.shortcuts import Symbol, And, Or, Not, BOOL, Iff, Xor

from cdcl_vsids import CDCLSolver
from flattern_bv import is_flat_cube, flattening
from tr import cnf_to_dimacs
from tseytin import tseitin_transformation


def bit_blasting(formula):
    """
    Perform bit-blasting on the given formula in bit-vector arithmetic.
    Assumes all bit-vectors have a width of 4.
    """
    atomic_vars = []  # Stores equality constraint Boolean variables
    boolean_vars = {}  # Map to hold the Boolean variables for each bit

    def create_boolean_variables(term):
        """
        Create 4 Boolean variables for the given bit-vector term.
        """
        if term not in boolean_vars:
            boolean_vars[term] = [Symbol(f"{str(term)}_{i}", BOOL) for i in
                                  range(4)]
        return boolean_vars[term]

    def bitwise_constraints(op, a_bits, b_bits, result_bits):
        """
        Generate bitwise constraints for the given bitwise operation (AND, OR).
        """
        constraints = []
        for i in range(4):  # Fixed width of 4 bits
            if op == "and":
                constraints.append(
                    Iff(result_bits[i], And(a_bits[i], b_bits[i])))
            elif op == "or":
                constraints.append(
                    Iff(result_bits[i], Or(a_bits[i], b_bits[i])))
        return constraints

    def addition_constraints(a_bits, b_bits):
        """
        Generate bitwise constraints for bit-vector addition.
        """
        result_bits = [Symbol(f"sum_{i}", BOOL) for i in range(4)]
        carry_bits = [Symbol(f"carry_{i}", BOOL) for i in
                      range(5)]  # One extra for carry out
        constraints = []
        # Carry-in at LSB is always 0
        constraints.append(Not(carry_bits[0]))
        for i in range(4):
            # Compute sum bit: sum[i] = a[i] ⊕ b[i] ⊕ carry[i]
            constraints.append(Iff(result_bits[i],
                                   Xor(Xor(a_bits[i], b_bits[i]),
                                       carry_bits[i])))
            # Compute carry bit: carry[i+1] = (a[i] & b[i]) | (carry[i] & (a[i] ⊕ b[i]))
            next_carry = Or(And(a_bits[i], b_bits[i]),
                            And(carry_bits[i], Xor(a_bits[i], b_bits[i])))
            constraints.append(Iff(carry_bits[i + 1], next_carry))
        return result_bits, constraints

    def handle_formula(formula):
        """
        Recursively process the formula to generate bit-blasted constraints.
        """
        if formula.is_symbol():
            return create_boolean_variables(formula), []

        elif formula.is_and() or formula.is_or():
            # Handle AND/OR operations by processing all subformulas
            all_constraints = []
            for subformula in formula.args():
                _, sub_constraints = handle_formula(subformula)
                all_constraints.extend(sub_constraints)
            return None, all_constraints

        elif formula.is_bv_and() or formula.is_bv_or():
            # Handle bitwise operations (AND/OR)
            a_bits, a_constraints = handle_formula(formula.arg(0))
            b_bits, b_constraints = handle_formula(formula.arg(1))
            result_bits = create_boolean_variables(formula)
            op = "and" if formula.is_bv_and() else "or"
            constraints = bitwise_constraints(op, a_bits, b_bits, result_bits)
            return result_bits, a_constraints + b_constraints + constraints

        elif formula.is_equals():
            # Handle bit-vector equality by ensuring all bits are equal
            a_bits, a_constraints = handle_formula(formula.arg(0))
            b_bits, b_constraints = handle_formula(formula.arg(1))

            eq_var = Symbol(f"{formula}_eq",
                            BOOL)  # Single Boolean variable representing equality
            atomic_vars.append(eq_var)

            bitwise_equality = [Iff(a_bits[i], b_bits[i]) for i in range(4)]
            equality_constraint = Iff(eq_var, And(bitwise_equality))

            return [eq_var], a_constraints + b_constraints + [
                equality_constraint]


        elif formula.is_not():
            # Handle logical NOT (!a)
            a_bits, a_constraints = handle_formula(formula.arg(0))
            if len(a_bits) != 1:
                raise ValueError(
                    "Logical NOT can only be applied to a single Boolean variable.")
            atomic_vars.append(Not(atomic_vars.pop()))

            result_var = Symbol(f"{formula}_not", BOOL)
            constraints = [Iff(result_var, Not(a_bits[0]))]

            return [result_var], a_constraints + constraints


        elif formula.is_constant():
            # Base case: Constant bit-vector
            constant_value = formula.constant_value()  # Extract the numeric value of the constant
            result_bits = create_boolean_variables(
                formula)  # Create Boolean variables for the constant
            constraints = []

            for i in range(4):  # Iterate over all 4 bits (fixed width)
                bit_value = (
                                    constant_value >> i) & 1  # Extract the i-th bit (0 or 1)
                if bit_value == 1:
                    # Represent True by directly constraining result_bits[i]
                    constraints.append(result_bits[i])
                else:
                    # Represent False by directly constraining result_bits[i]
                    constraints.append(Not(result_bits[i]))
            return result_bits, constraints

        elif formula.is_bv_add():
            a_bits, a_constraints = handle_formula(formula.arg(0))
            b_bits, b_constraints = handle_formula(formula.arg(1))
            result_bits, add_constraints = addition_constraints(a_bits, b_bits)
            return result_bits, a_constraints + b_constraints + add_constraints

        else:
            raise NotImplementedError(f"Unsupported operation: {formula}")

    # Start bit-blasting transformation
    _, constraints = handle_formula(formula)
    constraints.extend(atomic_vars)  # Add atomic equality constraints

    return And(constraints)


def bv_solver(formula):
    """
    1. Apply bit-blasting to convert the formula to a Boolean formula.
    2. Convert it to CNF using Tseitin transformation.
    3. Solve it using a CDCL solver.
    """
    if isinstance(formula, list):
        formula = And(formula)  # Convert list into a single formula
    if not is_flat_cube([formula] if formula.is_equals() else formula.args()):
        formula = flattening(formula)
    print("after flattening")
    print(formula)
    phi = bit_blasting(formula)
    print("ater bit blasting:")
    print(phi)
    cnf, var_to_int, int_to_var = cnf_to_dimacs(tseitin_transformation(phi))
    solver = CDCLSolver()
    result = solver.cdcl_solve(cnf)
    return result
