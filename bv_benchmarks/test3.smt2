(set-logic QF_BV)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const s (_ BitVec 4))
(declare-const t (_ BitVec 4))
(assert (=> (= (bvadd s t) s) (distinct (bvand s (bvadd s (bvand s #b0001))) (bvand s (bvadd s #b0001)))))
(check-sat)
(exit)