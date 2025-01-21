# importing system module for reading files
import sys

SAT = "sat"
UNSAT = "unsat"
COMMENT = "c"
PROBLEM = "p"
END = "0"

learn_clauses = []

lit_counter = {}


def init_lit_counter(f):
    for clause in f:
        for l in clause:
            lit_counter[l] = lit_counter.get(l, 0) + 1


# in what follows, a *formula* is a collection of clauses,
# a clause is a collection of literals,
# and a literal is a non-zero integer.

# input path:  a path to a cnf file
# output: the formula represented by the file,
#         the number of variables,
#         and the number of clauses
def parse_dimacs_path(path):
    count = 0
    lines = []
    with open(path, 'r') as file:
        for line in file:
            line = line.strip()
            if not line:
                continue
            literals = line.split()
            first_char = line[0]
            if first_char == PROBLEM:
                num_vars = int(literals[2])
                num_clauses = int(literals[3])
                continue
            if first_char == COMMENT:
                continue
            count += 1
            integer_line = [int(lit) for lit in literals if lit != END]
            lines.append(integer_line)
    return lines, num_vars, num_clauses





# input cnf: a formula
# input n_vars: the number of variables in the formula
# input n_clauses: the number of clauses in the formula
# output: True if cnf is satisfiable, False otherwise
def cdcl_solve(cnf, n_vars, n_clauses):
    m, f, d, k = [], cnf, [], "no"
    pre_m, pre_f, pre_d, pre_k = [], [], [], []
    num_conflict = 0

    while (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
        pre_m = m.copy() if m is not None else None
        pre_f = f.copy() if f is not None else None
        pre_d = d.copy() if d is not None else None
        pre_k = k.copy() if k != "no" and k is not None else "no" if k is not None else None

        m, f, d, k = fail(m, f, d, k)
        if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
            break

        if num_conflict > 700:  # like chaff
            m, f, d, k = restart(m, f, d, k)
            if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                num_conflict = 0
                continue

        m, f, d, k = conflict(m, f, d, k)
        if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
            num_conflict += 1

            # inc literal that were in the conflict
            for lit in k:
                lit_counter[lit] += 1
            # divide every after 265 conflicts
            if num_conflict % 256 == 0:
                for lit in lit_counter:
                    lit_counter[lit] //= 2
            continue

        m, f, d, k = explain(m, f, d, k)
        if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
            continue

        m, f, d, k = unit_propagate(m, f, d, k)
        if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
            continue

        m, f, d, k = learn(m, f, d, k)
        if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
            continue

        m, f, d, k = decide(m, f, d, k)
        if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
            continue

        m, f, d, k = backjump(m, f, d, k)
        if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
            continue

        m, f, d, k = forget(m, f, d, k)
        if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
            continue


    if k is None:
        return False
    if k == "no":
        return True
    return "unknown"


def restart(m, f, d, k):
    return [], f, [], "no"


def learn(m, f, d, k):
    global learn_clauses
    if k != "no" and k not in f and k not in learn_clauses:
        learn_clauses += [k]
        return m, f + [k], d, "no"
    return m, f, d, k


def forget(m, f, d, k):
    global learn_clauses
    if k == "no":
        for c in learn_clauses:
            if c in f:
                f_minus_c = [x for x in f if x not in c]
                return m, f_minus_c, d, k
    return m, f, d, k


def conflict(m, f, d, k):
    if k != "no":
        return m, f, d, k
    for clause in f:
        if model_conflict(m, [clause]):
            return m, f, d, clause
    return m, f, d, k


def explain(m, f, d, k):
    if k == "no":
        return m, f, d, k
    for lit in k:
        if -lit in m:
            for clause in [c for c in f if -lit in c]:
                c = [l for l in clause if l != -lit]
                conflict = model_conflict(m[:m.index(-lit)], [c])
                if conflict:
                    new_k = [l for l in list(set(k + c)) if l != lit]
                    new_k = new_k + [lit] if lit in c else new_k
                    if new_k != k:
                        return m, f, d, new_k
    return m, f, d, k


def backjump(m, f, d, k):
    if k == "no" or len(d) == 0:
        return m, f, d, k

    for l in k:
        for l0 in d:
            l0n = m[m.index(l0):]
            rest_model = m[:m.index(l0)]
            if all(-lit in rest_model for lit in k if lit != l) and -l in l0n:
                return rest_model + [l], f, [lit for lit in d if
                                             lit not in l0n], "no"
    return m, f, d, k


def unit_propagate(m, f, d, k):
    if m is None and f is None and d is None:
        return m, f, d, k

    for clause in f:
        for lit in clause:
            if lit not in m and -lit not in m and lit != 0:
                conflict = model_conflict(m, [[l for l in clause if l != lit]])
                if conflict:
                    m += [lit]
                    return m, f, d, k
    return m, f, d, k


def decide(m, f, d, k):
    if m == None and f == None and d == None:
        return m, f, d

    l = choose_lit_vsids(m)

    if l is None:
        return m, f, d, k

    d += [l]
    m += [l]
    return m, f, d, k



def fail(m, f, d, k):
    if len(d) == 0 and k != "no":
        return None, None, None, None
    return m, f, d, k




# input m: a model
# input f: a formula
# output: True if model m is satisfy negation of clause in f.
def model_conflict(m, f):
    for clause in f:
        conflict = True
        for lit in clause:
            if -lit not in m:
                conflict = False
                break
        if conflict:
            return True
    return False


def choose_lit_vsids(m):
    current_max=0
    chosen_lit=None
    for l,v in lit_counter.items():
        if l not in m and -l not in m:
            if v > current_max:
                current_max=v
                chosen_lit = l
    return chosen_lit






######################################################################

# get path to cnf file from the command line
path = sys.argv[1]

# parse the file
cnf, num_vars, num_clauses = parse_dimacs_path(path)

init_lit_counter(cnf)

# check satisfiability based on the chosen algorithm
# and print the result
result = cdcl_solve(cnf, num_vars, num_clauses)
print(SAT if result is True else UNSAT if result is False else "unkown")
