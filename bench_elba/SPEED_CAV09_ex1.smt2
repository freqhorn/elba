(declare-rel inv (Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var m0 Int)

(rule (=> (and (= x0 0) (= y0 0)) (inv x0 y0 m0)))

(rule (=> (and
        (inv x0 y0 m0)
        (< x0 100)
        (= y1 (ite (< y0 m0) (+ y0 1) y0))
        (= x1 (ite (< y0 m0) x0 (+ x0 1)))
        )
        (inv x1 y1 m0)
))

;Bound according to loopus paper: 100 + max(0, m)
