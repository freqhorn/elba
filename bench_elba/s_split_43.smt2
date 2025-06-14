(declare-rel inv (Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)

(rule (=> (and (= x0 0) (= y0 0)) (inv x0 y0)))

(rule (=> (and
        (inv x0 y0)
        (not (>= x0 100000000))
        (= x1 (+ 1 x0))
        (= y1 (ite (>= x0 50000000)
          (ite (>= x0 100000000) y0 (+ y0 1)) 0)))
    (inv x1 y1)))
