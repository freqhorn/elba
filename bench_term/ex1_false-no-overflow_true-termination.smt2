(declare-rel inv ( Int Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var r Int)
(declare-var r1 Int)

(declare-rel fail ())

(rule (inv x y 1))

(rule (=> 
    (and 
        (inv x y r)
        (> y 0)
        (= r1 (* r x))
        (= y1 (- y 1))
    )
    (inv x y1 r1)
  )
)

(rule (=> (and (inv x y r) (> y 0)) fail))

(query fail :print-certificate true)
