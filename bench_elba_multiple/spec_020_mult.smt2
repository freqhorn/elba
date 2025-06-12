(declare-rel inv (Int Int))
(declare-rel inv1 (Int Int))
(declare-rel inv2 (Int Int))
(declare-rel inv3 (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (inv x y))

(rule (=> (and (> x y) (inv x y)) (inv1 x y)))
(rule (=> (and (<= x y) (inv x y)) (inv3 x y)))

(rule (=>
    (and
        (inv1 x y)
        (> x 0)
        (= x1 (- x 1))
    )
    (inv1 x1 y)
  )
)

(rule (=> (and (<= x 0)  (inv1 x y)) (inv2 x y)))

(rule (=>
    (and
      (inv2 x y)
      (> y 0)
      (= y1 (- y 1))
    )
    (inv2 x y1)
  )
)

(rule (=>
    (and
      (inv3 x y)
      (> y 0)
      (= y1 (- y 1))
    )
    (inv3 x y1)
  )
)

(rule (=> (and (inv2 x y) (not (or (<= x 0) (<= y 0)))) fail))
(rule (=> (and (inv3 x y) (> y 0)) fail))

(query fail :print-certificate true)
