(declare-rel inv ( Int Int ))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(declare-rel fail ())

(rule (inv i j))

(rule (=> 
    (and 
        (inv i j)
        (<= i 100)
        (= i1 j)
        (= j1 (+ i 1))
    )
    (inv i1 j1)
  )
)

(rule (=> (and (inv  i j) (<= i 100)) fail))

(query fail :print-certificate true)
