(declare-rel inv ( Int Int Int))
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)
(declare-var r Int)

(declare-rel fail ())

(rule (=> (and (>= r 0) (= a (* 2 r)) (= b (* 2 r))) (inv a b r)))

(rule (=> 
    (and 
        (inv a b r)
        (>= a r)
        (or (and (= a1 (- a 1)) (= b1 b))
            (and (= a1 (- b 1)) (= b1 a1)))
    )
    (inv a1 b1 r)
  )
)

(rule (=> (and (inv a b r) (>= a r)) fail))

(query fail :print-certificate true)
