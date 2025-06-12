(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var d Int)
(declare-var d1 Int)

(declare-rel fail ())

(rule (inv x y d))

(rule (=> 
    (and 
        (inv x y d)
        (> x 0)
        (> y 0)
        (> d 0)
        (or
            (and (= x1 (- x 1)) (= y1 y))
            (and (= y1 (- y 1)) (= d1 (- d 1)))
        )
    )
    (inv x1 y1 d1)
  )
)

(rule (=> (and (inv x y d)
      (> x 0)
      (> y 0)
      (> d 0)
) fail))

(query fail :print-certificate true)
