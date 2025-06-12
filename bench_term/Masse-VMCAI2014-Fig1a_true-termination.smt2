(declare-rel inv ( Int Int ))
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)

(declare-rel fail ())

(rule (inv a b))

(rule (=> 
    (and 
        (inv a b)
        (>= a 0)
        (= a1 (+ a b))
        (= b1 (ite (>= b 0) (- (- 0 b) 1) (- 0 b)))
    )
    (inv a1 b1)
  )
)

(rule (=> (and (inv a b) (>= a 0)) fail))

(query fail :print-certificate true)
