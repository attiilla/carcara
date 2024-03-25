(set-logic QF_UF)

(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)

(assert (not a))
(assert (not b))
(assert (or a b (not (or c d))))
(assert (or a (not d)))
(assert (or a (not b)))
(assert (or b c d))

(check-sat)
