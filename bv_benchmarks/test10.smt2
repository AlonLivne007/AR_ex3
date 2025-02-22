(set-logic QF_BV)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const s (_ BitVec 4))
(declare-const t (_ BitVec 4))
(assert (or (distinct (bvor s (bvand s t)) s) (distinct (bvor (bvand s #b0001) (bvadd t t)) (bvadd t (bvadd t (bvand s #b0001))))))
(check-sat)
(exit)