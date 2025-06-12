(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (=> (and (= y 0) (= x 0)) (inv x y)))

(rule (=>
    (and
        (inv x y)
        (< x 8) (< y 8)
        (= x1 (+ x 1))
        (= y1 (+ y 2))
    )
    (inv x1 y1)
  )
)
