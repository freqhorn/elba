; pc = ite(x > y /\ x > 0, x, ite(y >= x /\ y > 0, y, 0))

(declare-rel inv1 (Int Int))
(declare-rel inv2 (Int Int))
(declare-rel inv (Int Int))

(declare-var x1 Int)
(declare-var y1 Int)
(declare-var x2 Int)
(declare-var y2 Int)

(declare-rel fail ())

(rule (inv x1 y1))

(rule (=> (and (> x1 y1) (inv x1 y1)) (inv1 x1 y1)))
(rule (=> (and (<= x1 y1) (inv x1 y1)) (inv2 x1 y1)))

(rule (=>
    (and
      (inv1 x1 y1)
      (> x1 0)
      (= x2 (- x1 1))
    )
    (inv1 x2 y1)
  )
)

(rule (=>
    (and
      (inv2 x1 y1)
      (> y1 0)
      (= y2 (- y1 1))
    )
    (inv2 x1 y2)
  )
)

(rule (=> (and (inv1 x1 y1) (> x1 0)) fail))
(rule (=> (and (inv2 x1 y1) (> y1 0)) fail))

(query fail :print-certificate true)
