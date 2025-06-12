(declare-rel inv ( Int Int Int))
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
        (>= x 0)
        (or (= x1 (+ x y)) (= x1 (+ x z)))
        (= y1 (+ y z))
        (= z1 (- z 1))
    )
    (inv x1 y1 z1)
  )
)
