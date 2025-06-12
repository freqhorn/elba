(declare-rel inv (Int Int))
(declare-var j Int)
(declare-var j0 Int)
(declare-var j1 Int)
(declare-var d Int)

(declare-rel fail ())

(rule (=> (and (= (* j0 d) j) (> j 0) (> d 0)) (inv j d)))

(rule (=> 
    (and 
        (inv j d)
        (not (= j 0))
        (= j1 (- j d))
    )
    (inv j1 d)
  )
)

(rule (=> (and (inv j d) (not (= j 0))) fail))

(query fail :print-certificate true)
