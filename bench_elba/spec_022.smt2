(declare-rel inv (Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)

(rule (=> (and (> x0 0) (< y0 0))
    (inv x0 y0)))

(rule (=> (and
        (inv x0 y0)
        (< y0 x0)
        (= x1 (+ x0 1))
        (= y1 (+ y0 2)))
    (inv x1 y1)))
