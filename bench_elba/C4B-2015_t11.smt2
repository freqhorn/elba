(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var n0 Int)
(declare-var m0 Int)

(rule (=> true (inv x0 y0 n0 m0)))

(rule (=> (and
        (inv x0 y0 n0 m0)
        (> n0 x0)
        (= y1 (ite (> m0 y0) (+ y0 1) y0))
        (= x1 (ite (> m0 y0) x0 (+ x0 1)))
        )
        (inv x1 y1 n0 m0)
))
