(declare-rel inv ( Int Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var N Int)

(rule (=> (and (<= y 0) (> N 0)) (inv x y N)))

(rule (=> (and (inv x y N)
        (not (= x 0))
        (= x1 (ite (< x N) (+ x 1) y)))
    (inv x1 y N)
    )
)
