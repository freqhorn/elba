(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (>= x 0)
        (>= y 0)
        (= x1 (- y 1))
        (= y1 (- x 1))
    )
    (inv x1 y1)
  )
)
