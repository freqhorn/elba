(declare-rel inv (Int Int Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var d1 Int)
(declare-var d2 Int)
(declare-var d3 Int)

(declare-rel fail ())

(rule (inv x y z 1 1 1))

(rule (=>
  (and
    (inv x y z d1 d2 d3)
    (> x 0)
    (> y 0)
    (> z 0)
    (or (and (= x1 (- x d1)) (= y1 y) (= z1 z))
      (and (= x1 x) (= y1 (- y d2)) (= z1 z))
      (and (= x1 x) (= y1 y) (= z1 (- z d3))))
  )
  (inv x1 y1 z1 d1 d2 d3)
))

(rule (=> (and (inv x y z d1 d2 d3) (> x 0) (> y 0) (> z 0)) fail))

(query fail :print-certificate true)
