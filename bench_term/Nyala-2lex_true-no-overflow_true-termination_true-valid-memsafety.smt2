(declare-rel inv (Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)
(declare-var d0 Int)
(declare-var d1 Int)
(declare-var d2 Int)

(declare-rel fail ())

(rule (inv j d))

(rule (=> 
    (and 
        (inv j d)
        (>= j 0)
        (>= d 0)
        (= d0 (- d 1))
        (= d1 (ite (< d0 0) d2 d0))
        (= j1 (ite (< d0 0) (- j 1) j))
    )
    (inv j1 d1)
  )
)

(rule (=> (and (inv j d) (>= j 0) (>= d 0)) fail))

(query fail :print-certificate true)
