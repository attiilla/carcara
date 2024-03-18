(set-logic QF_UF)

(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(declare-const f Bool)

(assert (not a))
(assert (or a d))
(assert (not b))
(assert (or a b (not (or c d e f))))

(check-sat)
