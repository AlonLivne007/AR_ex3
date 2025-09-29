# 🧠 DPLL(T)-Based SMT Solver Project

This project was developed as part of the *Automated Reasoning* course and implements a modular SMT solver architecture based on the **DPLL(T)** framework.  
It combines multiple theory solvers and SAT solving strategies to handle SMT-LIB problems, specifically for bit-vectors and congruence closure (equality logic).

---

## 🚀 How to Run

To run the solver on an SMT2 benchmark file:

```bash
python3 dpllt-solver.py bv_cube_benchmarks/test3.smt2
```

Make sure the input file is in SMT-LIB v2 format (`.smt2`), and that the required files are in the same directory or accessible via the project path.

---

## 🧩 Project Structure

- `dpllt-solver.py` – The main entry point combining SAT solving with theory solvers via the DPLL(T) architecture.
- `cdcl_solver1_vsids.py` / `cdcl_vsids.py` – CDCL SAT solvers using the VSIDS heuristic.
- `bv_solver.py` – Bit-Vector theory solver.
- `cc_solver.py` – Congruence closure solver (for equality with uninterpreted functions).
- `tseytin.py` – CNF conversion using Tseytin transformation.
- `tr.py` – Parser and transformer for SMT2 input.

---

## 🛠️ Features

- 🧮 **CDCL + VSIDS**: Conflict-driven clause learning SAT solver with VSIDS decision heuristic.
- 🧱 **Modular Theory Solvers**: Plug-and-play support for bit-vectors and equality logic.
- 🔄 **Tseytin Encoding**: Converts boolean formulas to CNF efficiently.
- 📜 **SMT2 Parsing**: Supports basic parsing of SMT-LIBv2 benchmarks.
- 🧠 **DPLL(T) Framework**: Integration of SAT and theory solvers in a standard architecture.

---

## 📁 Example Input

A sample SMT2 file might look like:

```smt
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x #x01) #x02))
(check-sat)
```

---

## 🧪 Sample Output

When running:

```bash
python3 dpllt-solver.py tests/test3.smt2
```

The output might be:

```
SAT
x = 1
```

(or `UNSAT` if constraints are contradictory)

---

## ✍️ Authors

This project was created as part of the "Automated Reasoning" course at BIU.

---

## 🤝 Contributing

Pull requests and suggestions are welcome!  
Feel free to fork the project or open an issue.

---
