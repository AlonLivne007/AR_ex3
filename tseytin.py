from pysmt.shortcuts import *
from pysmt.typing import BOOL

def tseitin_transformation(formula):
    p_c_map = {}
    clauses = set()
    i = 1

    def tseitin_subformula(c):

        nonlocal i

        if c in p_c_map:
            p_c = p_c_map[c]
        else:
            p_c = Symbol(f"P_{i}")
            p_c_map[c] = p_c
            i += 1

        if c.is_symbol():
            clauses.add(Or(Not(p_c), c))
            clauses.add(Or(Not(c), p_c))
            return

        if c == Bool(False):
            clauses.add(Or(Not(p_c), Bool(False)))
            clauses.add(Or(Bool(True), p_c))
            return
        if c == Bool(True):
            clauses.add(Or(Not(p_c), Bool(True)))
            clauses.add(Or(Bool(False), p_c))
            return

        if c.is_and():
            sub_clauses = c.args()
            for clause in sub_clauses:
                tseitin_subformula(clause)

            for clause in sub_clauses:
                clauses.add(Or(Not(p_c), p_c_map[clause]))
            clauses.add(Or([p_c] + [Not(p_c_map[cl]) for cl in sub_clauses]))

        elif c.is_or():
            sub_clauses = c.args()
            for clause in sub_clauses:
                tseitin_subformula(clause)

            for clause in sub_clauses:
                clauses.add(Or(Not(p_c_map[clause]), p_c))
            clauses.add(Or([Not(p_c)] + [p_c_map[cl] for cl in sub_clauses]))

        elif c.is_not():
            d = c.arg(0)
            tseitin_subformula(d)

            clauses.add(Or(Not(p_c), Not(p_c_map[d])))
            clauses.add(Or(p_c, p_c_map[d]))

        elif c.is_implies():
            c1, c2 = c.args()
            tseitin_subformula(c1)
            tseitin_subformula(c2)

            pc1, pc2 = p_c_map[c1], p_c_map[c2]

            clauses.add(Or(Not(p_c), Not(pc1), pc2))
            clauses.add(Or(p_c, pc1))
            clauses.add(Or(p_c, Not(pc2)))

        elif c.is_iff():
            c1, c2 = c.args()
            tseitin_subformula(c1)
            tseitin_subformula(c2)

            pc1, pc2 = p_c_map[c1], p_c_map[c2]

            clauses.add(Or(Not(p_c), pc1, Not(pc2)))
            clauses.add(Or(Not(p_c), Not(pc1), pc2))
            clauses.add(Or(p_c, Not(pc1), Not(pc2)))
            clauses.add(Or(p_c, pc1, pc2))

        else:
            raise ValueError(f"Unsupported operator: {c.node_type()}")

    tseitin_subformula(formula)
    clauses.add(p_c_map[formula])

    return And(list(clauses))


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

    formula5 = Iff(Not(A), Not(B))
    formula6 = A


    # Apply Tseitin transformation
    formula = formula2
    cnf_formula = tseytin_transformation(formula)
    print("formula:", formula)
    print("CNF formula:", cnf_formula)
