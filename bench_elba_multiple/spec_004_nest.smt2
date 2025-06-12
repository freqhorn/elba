(declare-rel itp1 (Int Int Int Int))
(declare-rel itp2 (Int Int Int Int))

(declare-var x1 Int)
(declare-var y1 Int)
(declare-var x2 Int)
(declare-var y2 Int)
(declare-var n Int)
(declare-var m Int)

(declare-rel fail ())

(rule (=> (and (= x1 n) (= y1 m) (> n 0) (> m 0)) (itp1 x1 y1 n m)))

(rule (=>
    (and
      (itp1 x1 y1 n m)
      (> x1 0)
      (= x2 (- x1 1))
      (= y2 m)
    )
    (itp2 x2 y2 n m)
  )
)

(rule (=>
    (and
      (itp2 x1 y1 n m)
      (> y1 0)
      (= y2 (- y1 1))
    )
    (itp2 x1 y2 n m)
  )
)

(rule (=> (and (itp2 x1 y1 n m) (<= y1 0)) (itp1 x1 y2 n m)))

(rule (=> (and (itp1 x1 y1 n m) (> y1 0)) fail))

(query fail :print-certificate true)
