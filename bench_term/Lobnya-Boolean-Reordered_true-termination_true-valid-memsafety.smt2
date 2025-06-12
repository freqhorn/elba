(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)

(declare-rel fail ())

(rule (=> (= x (+ y 2)) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (not (= y 0))
        (= x1 (- x 1))
        (= y1 (ite (>= x 0) 1 0))
    )
    (inv x1 y1)
  )
)

(rule (=> (and (inv x y) (not (= y 0))) fail))

(query fail :print-certificate true)
