import sys
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO
from pysmt.walkers import IdentityDagWalker
from pysmt.walkers.generic import handles
import pysmt.operators as op
from pysmt.shortcuts import Not, EqualsOrIff, Function, And, Symbol, BOOL, \
    BVType, get_env


class SubTermsGetter(IdentityDagWalker):
    def __init__(self, env):
        IdentityDagWalker.__init__(self, env=env, invalidate_memoization=True)
        self.sub_terms = set([])

    @handles(set(op.ALL_TYPES))
    def walk_collect(self, formula, args, **kwargs):
        self.sub_terms.add(formula)

def get_terms(cube):
    formula = And(cube)
    sub_terms_getter = SubTermsGetter(get_env())
    sub_terms_getter.walk(formula)
    return [t for t in sub_terms_getter.sub_terms if t.is_symbol() or t.is_function_application()]

def is_cube(cube):
    return all(is_lit(lit) for lit in cube)

def is_lit(term):
    """
    A literal in QF_BV is:
    - An equality (=)
    - A disequality (≠), which is Not(EqualsOrIff(...))
    """
    return term.is_equals() or (term.is_not() and term.args()[0].is_equals())

def is_flat_lit(lit):
    assert is_lit(lit)

    if lit.is_equals():
        left, right = lit.args()
        return left.is_symbol() and (right.is_symbol() or (right.is_function_application() and all(arg.is_symbol() for arg in right.args())))

    elif lit.is_not() and lit.args()[0].is_equals():
        left, right = lit.args()[0].args()
        return left.is_symbol() and right.is_symbol()

    return False

def is_flat_cube(cube):
    return is_cube(cube) and all(is_flat_lit(lit) for lit in cube)


def flattening(formula):
    cube = list(formula.args()) if formula.is_and() else [formula]
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




