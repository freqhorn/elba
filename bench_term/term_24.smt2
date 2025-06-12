(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var y2 Int)
(declare-var z Int)

(rule (=> (and (<= x z) (<= y z)) (inv x y z)))

(rule (=> 
    (and 
        (inv x y z)
        (not (= x y))
        (= x1 (+ x 1))
        (= y1 (+ y 1))
        (= x2 (ite (> x1 z) z x1))
        (= y2 (ite (> y1 z) (- y1 1) y1))
    )
    (inv x2 y2 z)
  )
)
