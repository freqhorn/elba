(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (> (+ x y) 0)
        (or (and (>= x 0) (< y (- 2147483647 x))) (and (< x 0) (> y (- -2147483648 x))))
        (or
            (and (> x 0) (= x1 (- x 1)) (= y1 y))
            (and (<= x 0) (> y 0) (= y1 (- y 1)) (= x1 x))
            (and (<= x 0) (<= y 0) (= y1 y) (= x1 x))
        )
    )
    (inv x1 y1)
  )
)
