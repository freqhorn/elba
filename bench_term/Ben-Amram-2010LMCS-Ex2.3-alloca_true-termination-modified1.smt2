(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(declare-rel fail ())

(rule (inv x y z))

(rule (=> 
    (and 
        (inv x y z)
        (> x 0)
        (> y 0)
        (> z 0)
        (or
            (and (> y x) (= x1 (+ z1 1)) (= y1 z))
            (and (<= y x) (= z1 (- z 1)) (= x1 (+ y1 1)))
        )
    )
    (inv x1 y1 z1)
  )
)

(rule (=> (and (inv x y z)
      (> x 0)
      (> y 0)
      (> z 0)
) fail))

(query fail :print-certificate true)
