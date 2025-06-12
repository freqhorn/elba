(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (inv x y z))

(rule (=> 
    (and 
        (inv x y z)
        (or (> x y) (> y z))
        (= x1 (- x 3))
        (= y1 (- y 2))
        (= z1 (- z 1))
    )
    (inv x1 y1 z1)
  )
)
