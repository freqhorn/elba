(declare-rel inv ( Int Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (inv 100 -1 1))

(rule (=> 
    (and 
        (inv x y z)
        (>= (+ x y z) 1)
        (= x1 (- x 1))
        (= y1 (- y 1))
        (= z1 (+ z 1))
    )
    (inv x1 y1 z1)
  )
)
