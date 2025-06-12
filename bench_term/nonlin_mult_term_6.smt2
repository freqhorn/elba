(declare-rel inv (Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)
(declare-var d1 Int)

(declare-rel fail ())

(rule (inv j d))

(rule (=> 
    (and 
        (inv j d)
        (> (* j d) 0)
        (= j1 (- j))
    )
    (inv j1 d)
  )
)

(rule (=> (and (inv j d) (> (* j d) 0)) fail))

(query fail :print-certificate true)
