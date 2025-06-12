(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (= x 10000) (= y 1))  (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (>= (- x y) 1)
        (= x1 (- x 2))
        (= y1 (+ y 3))
    )
    (inv x1 y1)
  )
)

(rule (=> (and (inv x y) (>= (- x y) 1)) fail))

(query fail :print-certificate true)
