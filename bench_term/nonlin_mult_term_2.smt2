(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)

(declare-rel fail ())

(rule (=> (and (> j 0) (> d 1)) (inv j d)))

(rule (=> 
    (and 
        (inv j d)
        (< j 100)
        (= j1 (* j d))
    )
    (inv j1 d)
  )
)

(rule (=> (and (inv j d) (< j 100) ) fail))

(query fail :print-certificate true)
