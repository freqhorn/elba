(declare-rel inv (Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)

(declare-rel fail ())

(rule (=> (and (> (div j d) 1) (> d 0)) (inv j d)))

(rule (=> 
    (and 
        (inv j d)
        (not (= j d))
        (= j1 (- j 1))
    )
    (inv j1 d)
  )
)

(rule (=> (and (inv j d) (not (= j d))) fail))

(query fail :print-certificate true)
