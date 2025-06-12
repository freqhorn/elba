(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (inv -7 2 8))

(rule (=> 
    (and 
        (inv x y z)
        (not (= x y))
        (= x1 (+ x y (- z)))
        (= y1 (* y 2))
        (= z1 (- z 1))
    )
    (inv x1 y1 z1)
  )
)
