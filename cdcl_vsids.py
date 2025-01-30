class CDCLSolver:
    def __init__(self):
        self.learn_clauses = []  # Local storage instead of a global variable
        self.lit_counter = {}  # Local storage instead of a global variable

    def init_lit_counter(self, f):
        """ Initialize literal counters based on the formula. """
        self.lit_counter = {}  # Reset counter for each new formula
        for clause in f:
            for l in clause:
                self.lit_counter[l] = self.lit_counter.get(l, 0) + 1

    def cdcl_solve(self, cnf):
        """
        Performs CDCL (Conflict-Driven Clause Learning) to determine SAT or UNSAT.
        """
        self.init_lit_counter(cnf)

        m, f, d, k = [], cnf, [], "no"
        pre_m, pre_f, pre_d, pre_k = [], [], [], []
        num_conflict = 0

        while (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
            pre_m = m.copy()
            pre_f = f.copy()
            pre_d = d.copy()
            pre_k = k if k != "no" else "no"

            m, f, d, k = self.fail(m, f, d, k)
            if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                break

            if num_conflict > 700:  # Restart heuristic
                m, f, d, k = self.restart(m, f, d, k)
                if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                    num_conflict = 0
                    continue

            m, f, d, k = self.conflict(m, f, d, k)
            if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                num_conflict += 1
                # Increase counter for literals involved in the conflict
                for lit in k:
                    self.lit_counter[lit] += 1
                # Decay scores periodically
                if num_conflict % 256 == 0:
                    for lit in self.lit_counter:
                        self.lit_counter[lit] //= 2
                continue

            m, f, d, k = self.explain(m, f, d, k)
            if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                continue

            m, f, d, k = self.unit_propagate(m, f, d, k)
            if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                continue

            m, f, d, k = self.learn(m, f, d, k)
            if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                continue

            m, f, d, k = self.decide(m, f, d, k)
            if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                continue

            m, f, d, k = self.backjump(m, f, d, k)
            if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                continue

            m, f, d, k = self.forget(m, f, d, k)
            if (pre_m, pre_f, pre_d, pre_k) != (m, f, d, k):
                continue

        return None if k is None else (m if k == "no" else None)

    def restart(self, m, f, d, k):
        return [], f, [], "no"

    def learn(self, m, f, d, k):
        if k != "no" and k not in f and k not in self.learn_clauses:
            self.learn_clauses.append(k)
            return m, f + [k], d, "no"
        return m, f, d, k

    def forget(self, m, f, d, k):
        if k == "no":
            for c in self.learn_clauses:
                if c in f:
                    f_minus_c = [x for x in f if x not in c]
                    return m, f_minus_c, d, k
        return m, f, d, k

    def conflict(self, m, f, d, k):
        if k != "no":
            return m, f, d, k
        for clause in f:
            if self.model_conflict(m, [clause]):
                return m, f, d, clause
        return m, f, d, k

    def explain(self, m, f, d, k):
        if k == "no":
            return m, f, d, k
        for lit in k:
            if -lit in m:
                for clause in [c for c in f if -lit in c]:
                    c = [l for l in clause if l != -lit]
                    conflict = self.model_conflict(m[:m.index(-lit)], [c])
                    if conflict:
                        new_k = [l for l in list(set(k + c)) if l != lit]
                        if lit in c:
                            new_k.append(lit)
                        if new_k != k:
                            return m, f, d, new_k
        return m, f, d, k

    def backjump(self, m, f, d, k):
        if k == "no" or len(d) == 0:
            return m, f, d, k

        for l in k:
            for l0 in d:
                l0n = m[m.index(l0):]
                rest_model = m[:m.index(l0)]
                if all(-lit in rest_model for lit in k if lit != l) and -l in l0n:
                    return rest_model + [l], f, [lit for lit in d if lit not in l0n], "no"
        return m, f, d, k

    def unit_propagate(self, m, f, d, k):
        if m is None and f is None and d is None:
            return m, f, d, k

        for clause in f:
            for lit in clause:
                if lit not in m and -lit not in m and lit != 0:
                    conflict = self.model_conflict(m, [[l for l in clause if l != lit]])
                    if conflict:
                        m.append(lit)
                        return m, f, d, k
        return m, f, d, k

    def decide(self, m, f, d, k):
        if m is None and f is None and d is None:
            return m, f, d

        l = self.choose_lit_vsids(m)
        if l is None:
            return m, f, d, k

        d.append(l)
        m.append(l)
        return m, f, d, k

    def fail(self, m, f, d, k):
        if len(d) == 0 and k != "no":
            return None, None, None, None
        return m, f, d, k

    def model_conflict(self, m, f):
        for clause in f:
            if all(-lit in m for lit in clause):
                return True
        return False

    def choose_lit_vsids(self, m):
        max_score = 0
        chosen_lit = None
        for lit, score in self.lit_counter.items():
            if lit not in m and -lit not in m:
                if score > max_score:
                    max_score = score
                    chosen_lit = lit
        return chosen_lit
