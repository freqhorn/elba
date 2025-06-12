(declare-rel inv (Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)

(declare-rel fail ())

(rule (=> (> d 1) (inv j d)))

(rule (=> 
    (and 
        (inv j d)
        (< j 100)
        (= j1 (ite (<= j 0) 1 (* j d)))
    )
    (inv j1 d)
  )
)

(rule (=> (and (inv j d) (< j 100)) fail))

(query fail :print-certificate true)
