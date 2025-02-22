(set-logic QF_BV)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const s (_ BitVec 4))
(declare-const t (_ BitVec 4))
(assert (distinct (bvmul t (bvadd s s)) (bvmul s (bvadd t t))))
(check-sat)
(exit)