(set-logic QF_UF)

(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(declare-const f Bool)

(assert (not b))
(assert (or a b (not (or c f))))
(assert (or b d (not a)))
(assert (not d))
(assert (or b c d e f))
(assert (or d (not c)))
(assert (or d (not e)))

(check-sat)
