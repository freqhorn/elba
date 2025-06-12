(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (> (+ x y) 0)
        (= x1 (ite (> x y) (- x 1) (ite (= x y) (- x 1) x)))
        (= y1 (ite (> x y) y  (ite (= x y) y (- y 1))))
    )
    (inv x1 y1)
  )
)

(rule (=> (and (inv x y)
  (> (+ x y) 0))
fail))

(query fail :print-certificate true)
