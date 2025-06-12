(declare-rel inv (Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var c0 Int)

(rule (=> (and (= x0 0) (= c0 5000) (= y0 c0) ) (inv x0 y0 c0)))

(rule (=> (and
        (inv x0 y0 c0)
        (not (= x0 (* 2 c0)))
        (= x1 (+ x0 1))
        (= y1 (ite (>= x0 c0) (+ y0 1) (- y0 1))))
    (inv x1 y1 c0)))
