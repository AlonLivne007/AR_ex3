# importing system module for reading files
import sys

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
    m = set([frozeset([t]) for t in sub_term])
    f = flat_cube
    return m, f

class DisJointSets():
    def __init__(self,terms):
        # Initially, all elements are single element subsets
        self._parents = {t: t for t in terms}
        self._ranks = {t: 1 for t in terms}

    def find(self, u):
        while u != self._parents[u]:
            # path compression technique
            self._parents[u] = self._parents[self._parents[u]]
            u = self._parents[u]
        return u

    def union(self, u, v):
        # Union by rank optimization
        root_u, root_v = self.find(u), self.find(v)
        if root_u == root_v:
            return True
        if self._ranks[root_u] > self._ranks[root_v]:
            self._parents[root_v] = root_u
        elif self._ranks[root_v] > self._ranks[root_u]:
            self._parents[root_u] = root_v
        else:
            self._parents[root_u] = root_v
            self._ranks[root_v] += 1
        return False

# global list of all equalities and distincts
equalities = []
distincts = []

def uf_solver(flat_cube):
    assert is_flat_cube(flat_cube)
    terms = get_terms(flat_cube)
    disjointset = DisJointSets(terms)
    # union all equalities
    for eq in equalities:
        left, right = eq.args()
        disjointset.union(left, right)

    # union equalities arguments of function
    func_args = {}
    for x in terms:
        if x.is_function_application():
            fn = x.function_name()
            func_args.setdefault(fn, []).append(x.args()[0])

    for key, values in func_args.items():
        arg = {}
        for x in values:
            if disjointset.find(x) in arg:
                y = arg[disjointset.find(x)]
                disjointset.union(Function(key, [x]), Function(key, [y]))
            else:
                arg[disjointset.find(x)] = x

    # check if distinct equation in same group
    for eq in distincts:
        left, right = eq.args()[0].args()
        if disjointset.find(left) == disjointset.find(right):
            return False
    return True

def init_equalities(cube):
    global equalities, distincts
    for l in cube:
        if l.is_equals():
            equalities += [l]
        elif l.is_not() and l.args()[0].is_equals():
            distincts += [l]


# main function
def main():
    # read path from input
    path = sys.argv[1]
    with open(path, "r") as f:
        smtlib = f.read()

    # parse the smtlib file and get a formula
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(smtlib))
    formula = script.get_last_formula()

    # we are assuming `formula` is a flat cube.
    # `cube` represents `formula` as a list of literals
    cube = formula.args()

    # check if sat or unsat and print result
    init_equalities(cube)

    sat = uf_solver(cube)
    print("sat" if sat else "unsat")


if __name__ == "__main__":
    main()
