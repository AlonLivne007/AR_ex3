import sys
from pysmt.smtlib.parser import SmtLibParser

def bv_solver(formula):
    return true


filepath = sys.argv[1]
parser = SmtLibParser()
with open(filepath, "r") as f:
    script = parser.get_script(f)
    formula = script.get_last_formula()
    print(formula)  # Outputs the parsed formula
