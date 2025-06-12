(declare-rel inv (Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)

(rule (=> (and (> j 0) (> d 1)) (inv j d)))

(rule (=> 
    (and 
        (inv j d)
        (< j 10)
        (= j1 (* -2 j d))
    )
    (inv j1 d)
  )
)
