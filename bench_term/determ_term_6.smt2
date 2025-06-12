(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (inv 8 9 -2))

(rule (=> 
    (and 
        (inv x y z)
        (not (= (+ x y z) 0))
        (= x1 (+ (- y) 1))
        (= y1 (+ (* 2 x) z))
        (= z1 (* z 3))
    )
    (inv x1 y1 z1)
  )
)
