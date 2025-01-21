(set-logic QF_BV)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const s (_ BitVec 4))
(declare-const t (_ BitVec 4))
(assert (=> (distinct (bvor s (bvadd s (bvadd s #b0001))) (bvor s (bvadd s (bvor s #b0001)))) (distinct (bvadd t (bvor #b0001 (bvadd s s))) (bvadd s (bvadd s (bvadd t #b0001))))))
(assert (=> (distinct (bvadd t (bvor #b0001 (bvadd s s))) (bvadd s (bvadd s (bvadd t #b0001)))) (distinct (bvor s (bvadd s (bvadd s #b0001))) (bvor s (bvadd s (bvor s #b0001))))))
(check-sat)
(exit)