(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (>= x 0) (>= y 0)) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (or (> (- x y) 2) (> (- y x) 2))
        (= x1 (ite (< x y) (+ x 1) x))
        (= y1 (ite (< x y) y (+ y 1)))
    )
    (inv x1 y1)
  )
)

(rule (=> (and (inv x y) (or (> (- x y) 2) (> (- y x) 2))) fail))

(query fail :print-certificate true)
