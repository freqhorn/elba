(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)


(declare-rel fail ())

(rule (inv x y))

(rule (=>
  (and
    (inv x y)
    (> (+ x y) 0)
    (= x1 (+ (* -5 x) 18))
    (= y1 (+ (* -6 y) 13))
  )
  (inv x1 y1)
))

(rule (=> (and (inv x y) (> (+ x y) 0)) fail))

(query fail :print-certificate true)
