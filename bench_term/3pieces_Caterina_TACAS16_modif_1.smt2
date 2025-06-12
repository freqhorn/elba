(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(rule (=> (<= y 0) (inv x y)))

(rule (=>
    (and (inv x y)
        (not (= x 0))
        (= x1 (ite (< x 10) (+ x 1) y))
    )
    (inv x1 y)
))
