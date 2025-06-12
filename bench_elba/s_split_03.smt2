(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var w1 Int)
(declare-var z0 Int)
(declare-var w0 Int)

(rule (=> (and (= y0 0) (= w0 0) (> y0 z0)) (inv x0 y0 z0 w0)))

(rule (=> (and
        (inv x0 y0 z0 w0)
        (not (> x0 (+ y0 z0)))
        (= x1 (+ 1 x0))
        (= w1 (ite (< x0 z0) (+ w0 1) (- w0 2))))
    (inv x1 y0 z0 w1)))
