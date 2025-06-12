(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var y2 Int)
(declare-var r Bool)
(declare-var r1 Bool)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (not (= x 0))
        (> y 0)
        (= x1 (ite (> x 0) (ite r (- x 1) x) (ite r1 (+ x 1) x2)))
        (= y1 (ite (> x 0) (ite r y2 (- y 1)) (ite r1 y (- y 1))))
    )
    (inv x1 y1)
  )
)
