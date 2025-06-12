(declare-rel inv (Int))
(declare-var j Int)
(declare-var j1 Int)

(declare-rel fail ())

(rule (=> (> j 0) (inv j)))

(rule (=> 
    (and 
        (inv j)
        (not (= j 0))
        (= j1 (- j 1))
    )
    (inv j1)
  )
)

(rule (=> (and (inv j) (not (= j 0))) fail))

(query fail :print-certificate true)
