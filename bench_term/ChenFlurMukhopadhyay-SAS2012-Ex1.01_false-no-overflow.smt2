(declare-rel inv ( Int ))
(declare-var x Int)
(declare-var x1 Int)


(declare-rel fail ())

(rule (inv x ))

(rule (=> 
    (and 
        (inv x )
        (> x 0)
        (= x1 (+ (* -2 x) 10))
    )
    (inv x1 )
  )
)

(rule (=> (and (inv x ) (> x 0)) fail))

(query fail :print-certificate true)
