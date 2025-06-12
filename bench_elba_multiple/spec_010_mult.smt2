(declare-rel inv1 (Int Int))
(declare-rel inv2 (Int Int))
(declare-rel inv3 (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (> x y) (inv1 x y)))

(rule (=>
    (and
        (inv1 x y)
        (not (= x y))
        (= x1 (- x 2))
        (= y1 (- y 1))
    )
    (inv1 x1 y1)
  )
)

(rule (=> (and (= x y) (inv1 x y)) (inv2 x y)))

(rule (=>
    (and
      (inv2 x y)
      (> y 0)
      (= y1 (- y 1))
    )
    (inv2 x y1)
  )
)

(rule (=> (and (<= y 0) (inv2 x y)) (inv3 x y)))

(rule (=>
    (and
      (inv3 x y)
      (> x 0)
      (= x1 (- x 1))
    )
    (inv3 x1 y)
  )
)

(rule (=> (and (inv3 x y) (> x 0) (> y 0)) fail))

(query fail :print-certificate true)
