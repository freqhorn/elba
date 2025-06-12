(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (inv 4 -5 1))

(rule (=> 
    (and 
        (inv x y z)
        (not (= (+ x y) z))
        (= x1 (* x -3))
        (= y1 (+ y 2))
        (= z1 (- z 36))
    )
    (inv x1 y1 z1)
  )
)
