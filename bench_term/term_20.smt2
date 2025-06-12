(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var x1 Int)
(declare-var y1 Int)
(declare-var z1 Int)

(rule (=> (and (= x 0) (= y 0) (= z 0)) (inv x y z)))

(rule (=> 
    (and 
        (inv x y z)
        (< x 100)
        (= x1 (+ x y))
        (= y1 (+ z 1))
        (= z1 (- y1 1))
    )
    (inv x1 y1 z1)
  )
)
