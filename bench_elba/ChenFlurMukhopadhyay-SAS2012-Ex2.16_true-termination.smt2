(declare-rel inv (Int Int ))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)

(rule (=> true (inv x0 y0)))

(rule (=> (and
        (inv x0 y0)
        (> x0 0)
        (= x1 y0)
        (= y1 (- y0 1)))
    (inv x1 y1)))

; nonlinear