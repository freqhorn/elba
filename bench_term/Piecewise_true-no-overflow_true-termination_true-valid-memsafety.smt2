(declare-rel inv ( Int Int ))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(rule (inv i j))

(rule (=> 
    (and 
        (inv i j)
        (> j 0) (> i 0) (not (= i j))
        (or (and (< j i) (= j1 (- j 1))) (and (>= j i) (= i1 (- i 1))))
    )
    (inv i1 j1)
  )
)
