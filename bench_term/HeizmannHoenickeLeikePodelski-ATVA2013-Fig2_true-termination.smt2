(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (=> (= x (+ y 42)) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (>= x 0)
        (= y1 (- (* 2 y) x))
        (= x1 (div (+ x y1) 2))
    )
    (inv x1 y1)
  )
)
