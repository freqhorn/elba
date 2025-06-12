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
        (or (>= j 0) (>= d 0))
        (or (and (>= j 0) (= j1 (- j 1)) (= d1 d))
            (and (< j 0) (= j1 j) (= d1 (- d 1))))
    )
    (inv j1 d1)
  )
)

(rule (=> (and (inv j d) (or (>= j 0) (>= d 0))) fail))

(query fail :print-certificate true)
