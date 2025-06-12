(declare-rel inv (Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var res0 Int)
(declare-var res1 Int)

(rule (=> (= res0 0) (inv x0 y0 res0)))

(rule (=> (and
        (inv x0 y0 res0)
        (> x0 y0)
        (= res1 (+ res0 1))
        (= y1 (+ 1 x0)))
    (inv x0 y1 res1)))
