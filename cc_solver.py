# importing system module for reading files
import sys
from tr import flattening

# import classes for parsing smt2 files
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO
from pysmt.walkers import IdentityDagWalker
from pysmt.walkers.generic import handles
import pysmt.operators as op
from pysmt.shortcuts import get_env

# import pysmt functions for creating formulas and terms
from pysmt.shortcuts import Not, EqualsOrIff, Function, And, Symbol, BOOL


# helper class
class SubTermsGetter(IdentityDagWalker):
    def __init__(self, env):
        IdentityDagWalker.__init__(self, env=env, invalidate_memoization=True)
        self.sub_terms = set([])

    @handles(set(op.ALL_TYPES))
    def walk_collect(self, formula, args, **kwargs):
        self.sub_terms.add(formula)


# helper class
class FunctionSymbolsGetter(IdentityDagWalker):
    def __init__(self, env):
        IdentityDagWalker.__init__(self, env=env, invalidate_memoization=True)
        self.funs = set([])

    def walk_function(self, formula, args, **kwargs):
        function_name = formula.function_name()
        self.funs.add(function_name)

    @handles(set(op.ALL_TYPES) - set([op.FUNCTION]))
    def default(self, formula, args, **kwargs):
        return formula

# get all function symbols in a cube.
# for example: get_function_symbols([x=y, f(x)=z]) = [f]
def get_function_symbols(cube):
  formula = And(cube)
  function_symbols_getter = FunctionSymbolsGetter(get_env())
  function_symbols_getter.walk(formula)
  return function_symbols_getter.funs

# get all terms in a cube.
# for example: get_terms([x=y, f(x)=z]) = [x, y, z, f(x)]
def get_terms(cube):
  formula = And(cube)
  sub_terms_getter = SubTermsGetter(get_env())
  sub_terms_getter.walk(formula)
  return [t for t in sub_terms_getter.sub_terms if t.is_symbol() or t.is_function_application()]

def is_flat_lit(lit):
    assert is_lit(lit)

    if lit.is_equals():
        left, right = lit.args()
        return left.is_symbol() and (right.is_symbol() or
                                     (right.is_function_application() and all(arg.is_symbol() for arg in right.args())))

    elif lit.is_not() and lit.args()[0].is_equals():
        left, right = lit.args()[0].args()
        return left.is_symbol() and right.is_symbol()

    elif lit.is_function_application() and lit.get_type() == BOOL:
        return all(arg.is_symbol() for arg in lit.args())

    elif lit.is_not() and lit.args()[0].is_function_application() and lit.args()[0].get_type() == BOOL:
        return all(arg.is_symbol() for arg in lit.args()[0].args())
    return False

# check if `cube` is indeed a cube (that is, a list of literals)
def is_cube(cube):
  for lit in cube:
    if not is_lit(lit):
      return False
  return True

# check if `term` is a literal (equality or negation of equality)
def is_lit(term):
  return term.is_equals() or \
         (term.is_not() and (term.args()[0].is_equals() or (term.args()[0].is_function_application() and term.args()[0].get_type() == BOOL))) or \
         (term.is_function_application() and term.get_type() == BOOL)

# check if `cube` is a flat cube
def is_flat_cube(cube):
  if not is_cube(cube):
    return False
  for lit in cube:
    if not is_flat_lit(lit):
      return False
  return True

# check if `cube` is a flat cube
def is_flat_cube(cube):
  if not is_cube(cube):
    return False
  for lit in cube:
    if not is_flat_lit(lit):
      return False
  return True

def get_the_init_configuration_off(flat_cube):
    sub_term = get_terms(flat_cube)
    m = set([frozenset([t]) for t in sub_term])
    f = flat_cube
    return m, f

def unify(m, X, Y):
    union = X.union(Y)
    m.remove(X)
    m.remove(Y)
    m.add(frozenset(union))
    return m


def top_level(m, f):
    for x in m:
        for y in m:
            for eq in equalities:
                left, right = eq.args()
                if left in x and right in y and x != y:
                    return unify(m, x, y), f
    return m, f

def congruence(m, f):
    function_symbol = get_function_symbols(f)
    for z in m:
        for z1 in z:
            for z2 in z:
                for fn in function_symbol:
                    f_z1 = Function(fn, [z1])
                    f_z2 = Function(fn, [z2])
                    x = [x for x in m if f_z1 in x]
                    y = [x for x in m if f_z2 in x]
                    if x and y and x != y:
                        return unify(m, x[0], y[0]), f
    return m, f

def fail(m, f):
    for x in m:
        for eq in distincts:
            left, right = eq.args()[0].args()
            if left in x and right in x:
                return None, None
    return m, f


def uf_solver(flat_cube):
    # flat_cube = flattening(cube)
    step = 0

    m, f = get_the_init_configuration_off(flat_cube)
    pre_m, pre_f = set([]), []
    init_equalities(flat_cube)

    while (pre_m, pre_f) != (m, f):
        # print("******************************")
        # print("step: ", step)
        # print("m: ", m)
        # print("f: ", f)
        # print()
        step += 1
        if m is None or f is None:
            return m

        pre_m = m.copy()
        pre_f = f

        m, f = top_level(m, f)
        if (pre_m, pre_f) != (m, f):
            continue

        m, f = congruence(m, f)
        if (pre_m, pre_f) != (m, f):
            continue

        m, f = fail(m, f)
        if (pre_m, pre_f) != (m, f):
            continue
    return m

# global list of all equalities and distincts
equalities = []
distincts = []

def init_equalities(cube):
    global equalities, distincts
    for l in cube:
        if l.is_equals():
            equalities += [l]
        elif l.is_not() and l.args()[0].is_equals():
            distincts += [l]
