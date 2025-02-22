(set-logic QF_BV)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const s (_ BitVec 4))
(declare-const t (_ BitVec 4))
(assert (or (distinct (bvand s (bvor t (bvand s t))) (bvand s t)) (distinct (bvadd #b0001 (bvand s (bvadd s #b0001))) (bvor #b0001 (bvand s (bvadd s #b0001))))))
(check-sat)
(exit)