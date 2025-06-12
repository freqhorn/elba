(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var t0 Int)
(declare-var t1 Int)
(declare-var n0 Int)
(declare-var b0 Int)

(rule (=> (= t0 (ite (>= b0 1) 1 (- 1))) (inv x0 t0 n0 b0)))

(rule (=> (and
        (inv x0 t0 n0 b0)
        (and (> x0 (- n0)) (< x0 n0))
        (= x1 (ite (>= b0 1) (+ x0 t0) (- x0 t0)))
        )
        (inv x1 t0 n0 b0)
))
