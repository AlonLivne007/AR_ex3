(set-logic QF_BV)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const s (_ BitVec 4))
(declare-const t (_ BitVec 4))
(assert (distinct (bvor s (bvand #b0001 (bvmul s s))) s))
(check-sat)
(exit)