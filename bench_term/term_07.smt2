(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x 0))

(rule (=> 
    (and 
        (inv x y)
        (> x 0)
        (= x1 (ite (= y 2) (- x 3) (+ x 1)))
        (= y1 (ite (= y 2) 0 (+ y 1)))
    )
    (inv x1 y1)
  )
)
