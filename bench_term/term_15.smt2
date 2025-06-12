(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (= (div x 50) y)
        (= x1 (+ x 51))
        (= y1 (+ y 1))
    )
    (inv x1 y1)
  )
)
