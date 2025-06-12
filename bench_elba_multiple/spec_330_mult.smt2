(declare-rel inv (Int Int Int))
(declare-rel inv1 (Int Int Int))
(declare-rel inv2 (Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var z0 Int)
(declare-var z1 Int)

(declare-rel fail ())

(rule (inv x0 y0 z0))

(rule (=> (and
          (inv x0 y0 z0)
          (and (> y0 0) (> z0 0))
          (= x1 (ite (> x0 0) (- x0 1) x0))
          (= y1 (ite (> x0 0) y0 (- y0 1)))
          (= z1 (ite (> x0 0) z0 (- z0 1)))
          )
        (inv x1 y1 z1)
    )
)

(rule (=> (and (not (and (> y0 0) (> z0 0))) (inv x0 y0 z0)) (inv1 x0 y0 z0)))

(rule (=>
  (and
    (inv1 x0 y0 z0)
    (> y0 0)
    (= y1 (- y0 1))
  )
  (inv1 x0 y1 z0)
))

(rule (=> (and (not (> y0 0)) (inv1 x0 y0 z0)) (inv2 x0 y0 z0)))

(rule (=>
  (and
    (inv2 x0 y0 z0)
    (> z0 0)
    (= z1 (- z0 1))
  )
  (inv2 x0 y0 z1)
))

(rule (=> (and (inv2 x0 y0 z0) (<= x0 0) (<= y0 0) (<= z0 0)) fail))

(query fail :print-certificate true)
