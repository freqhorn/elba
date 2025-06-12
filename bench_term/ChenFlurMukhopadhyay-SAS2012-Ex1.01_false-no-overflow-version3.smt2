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
        (< x 0)
        (> y 0)
        (= x1 (- (* -3 x) 17))
        (= y1 (+ (* -4 x) 8))
    )
    (inv x1 y1)
  )
)

(rule (=> (and (inv x y) (< x 0) (> y 0)) fail))

(query fail :print-certificate true)
