(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)

(declare-rel fail ())

(rule (=> (> d 1) (inv 1 d)))

(rule (=> 
    (and 
        (inv j d)
        (< j 10000000)
        (= j1 (* j d))
    )
    (inv j1 d)
  )
)

(rule (=> (and (inv j d) (< j 10000000) ) fail))

(query fail :print-certificate true)
