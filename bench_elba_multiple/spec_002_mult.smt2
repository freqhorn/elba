; Three loops. First loop executes z times. Only one of the two remaining loops executes.
; Which one is determined by the initial value of x.

(declare-rel inv1 (Int Int Int))
(declare-rel inv2 (Int Int Int))
(declare-rel inv3 (Int Int Int))
(declare-rel inv (Int Int Int))

(declare-var x1 Int)
(declare-var y1 Int)
(declare-var z1 Int)
(declare-var x2 Int)
(declare-var y2 Int)
(declare-var z2 Int)

(declare-rel fail ())

(rule (=> (and (> x1 0) (> y1 0) (> z1 0)) (inv1 x1 y1 z1)))

(rule (=>
    (and
      (inv1 x1 y1 z1)
      (> z1 0)
      (= z2 (- z1 1))
    )
    (inv1 x1 y1 z2)
  )
)

(rule (=> (and (not (> z1 0)) (inv1 x1 y1 z1)) (inv x1 y1 z1)))

(rule (=> (and (> x1 5) (inv x1 y1 z1)) (inv2 x1 y1 z1)))
(rule (=> (and (<= x1 5) (inv x1 y1 z1)) (inv3 x1 y1 z1)))

(rule (=>
    (and
      (inv2 x1 y1 z1)
      (> x1 0)
      (= x2 (- x1 1))
    )
    (inv2 x2 y1 z1)
  )
)

(rule (=>
    (and
      (inv3 x1 y1 z1)
      (> y1 0)
      (= y2 (- y1 1))
    )
    (inv3 x1 y2 z1)
  )
)

(rule (=> (and (inv2 x1 y1 z1) (> x1 0)) fail))
(rule (=> (and (inv3 x1 y1 z1) (> y1 0)) fail))

(query fail :print-certificate true)
