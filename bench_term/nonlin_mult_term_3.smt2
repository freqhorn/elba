(declare-rel inv (Int Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)
(declare-var d1 Int)
(declare-var m Int)
(declare-var m1 Int)

(rule (=> (and (> j 1) (> m 1) (> d 1)) (inv j m d)))

(rule (=> 
    (and 
        (inv j m d)
        (< j 1000000)
        (= j1 (* j m d))
    )
    (inv j1 m d)
  )
)
