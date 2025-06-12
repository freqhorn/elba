(declare-rel inv (Int Int ))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)

(rule (=> (= y0 23) (inv x0 y0)))

(rule (=> (and
        (inv x0 y0)
        (>= x0 y0)
        (= x1 (- x0 1)))
    (inv x1 y0)))
