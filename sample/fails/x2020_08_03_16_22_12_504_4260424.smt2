; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --multi-trigger-linear --no-statistics --random-seed=1 --lang=smt2 --continued-execution --tlimit 211
(set-option :produce-unsat-cores true)
(set-logic AUFLIA)
(declare-sort S$ 0)
(declare-sort Nat$ 0)
(declare-sort Enat$ 0)
(declare-fun f$ () S$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun less$ (Nat$ Nat$) Bool)
(declare-fun zero$ () Enat$)
(declare-fun delta$ () Nat$)
(declare-fun less$a (Enat$ Enat$) Bool)
(declare-fun times$ (Enat$ Enat$) Enat$)
(declare-fun zero$a () Nat$)
(declare-fun infinity$ () Enat$)
(declare-fun the_enat$ (Enat$) Nat$)
(declare-fun arity_sym$ (S$) Enat$)
(assert (! (not (= (enat$ (the_enat$ (times$ (enat$ delta$) (arity_sym$ f$)))) (times$ (enat$ delta$) (arity_sym$ f$)))) :named a0))
(assert (! (= zero$ (enat$ zero$a)) :named a1))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (= (times$ ?v0 ?v1) infinity$) (or (and (= ?v0 infinity$) (not (= ?v1 zero$))) (and (= ?v1 infinity$) (not (= ?v0 zero$)))))) :named a2))
(assert (! (forall ((?v0 S$)) (=> (less$ zero$a delta$) (not (= (arity_sym$ ?v0) infinity$)))) :named a3))
(assert (! (forall ((?v0 Enat$)) (= (not (less$a zero$ ?v0)) (= ?v0 zero$))) :named a4))
(assert (! (forall ((?v0 Nat$)) (= (not (less$ zero$a ?v0)) (= ?v0 zero$a))) :named a5))
(assert (! (forall ((?v0 Nat$)) (not (= infinity$ (enat$ ?v0)))) :named a6))
(assert (! (forall ((?v0 Enat$)) (=> (not (= ?v0 infinity$)) (= (enat$ (the_enat$ ?v0)) ?v0))) :named a7))
(check-sat)
