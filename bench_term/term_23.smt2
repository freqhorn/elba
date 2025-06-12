(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (=> (>= x y) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (not (= x y))
        (= x1 (- x 1))
        (= y1 (+ y 1))
        (= x2 (ite (< x1 y1) (+ x1 15) x1))
    )
    (inv x2 y1)
  )
)
