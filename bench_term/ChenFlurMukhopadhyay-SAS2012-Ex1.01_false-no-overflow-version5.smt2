(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)


(declare-rel fail ())

(rule (=> (and (> x 0) (> y 0)) (inv x x)))

(rule (=>
  (and
    (inv x y)
    (> x 0)
    (= x1 (+ (* -5 x) (* -6 y) 18))
  )
  (inv x1 y)
))

(rule (=> (and (inv x y) (> x 0)) fail))

(query fail :print-certificate true)
