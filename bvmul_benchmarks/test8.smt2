(set-logic QF_BV)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const s (_ BitVec 4))
(declare-const t (_ BitVec 4))
(assert (distinct (bvand s (bvmul s (bvand s #b0001))) (bvmul s (bvand s #b0001))))
(check-sat)
(exit)