(set-logic QF_UF)

(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)

(assert (not a))
(assert (or a b))
(assert (or a c (not b)))
(assert (or a (not b) (not c)))

(check-sat)
