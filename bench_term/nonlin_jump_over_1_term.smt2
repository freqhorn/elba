(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(rule (=> (> y 1) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (>= x y)
        (= x1 (ite (= (mod x y) 1) (+ x 1) (- x 2)))
    )
    (inv x1 y)
  )
)
