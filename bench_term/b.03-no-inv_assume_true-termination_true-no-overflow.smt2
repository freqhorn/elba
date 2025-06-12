(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(rule (=> 
	(> x 0)
	(inv x y ))
)

(rule (=> 
    (and 
        (inv x y)
        (> x y)
        (<= (- 2147483647 x) y)
        (= y1 (+ y x))
        (= x1 x)
    )
    (inv x1 y1)
  )
)


