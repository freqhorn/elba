(declare-rel itp1 (Int Int Int))
(declare-rel itp2 (Int Int Int))
(declare-rel itp3 (Int Int Int))

(declare-var x1 Int)
(declare-var y1 Int)
(declare-var z1 Int)
(declare-var x2 Int)
(declare-var y2 Int)
(declare-var z2 Int)

(declare-rel fail ())

(rule (=> (and (= x1 0) (= y1 0) (= z1 0)) (itp1 x1 y1 z1)))

(rule (=>
    (and
      (itp1 x1 y1 z1)
      (< x1 10)
      (= y2 0)
    )
    (itp2 x1 y2 z1)
  )
)

(rule (=>
    (and
      (itp2 x1 y1 z1)
      (< y1 10)
      (= x2 x1)
      (= z2 0)
    )
    (itp3 x2 y2 z2)
  )
)

(rule (=>
    (and
      (itp3 x1 y1 z1)
      (< z1 10)
      (= z2 (+ z1 1))
      (= x2 x1)
      (= y2 y1)
    )
    (itp3 x2 y2 z2)
  )
)

(rule (=> (and (itp3 x1 y1 z1) (= y2 (+ y1 1)) (>= z1 10)) (itp2 x1 y2 z1)))

(rule (=> (and (itp2 x1 y1 z1) (= x2 (+ x1 1)) (>= y1 10)) (itp1 x2 y1 z1)))

(rule (=> (and (itp1 x1 y1 z1) (>= x1 10) (>= y1 10) (>= z1 10)) fail))

(query fail :print-certificate true)
