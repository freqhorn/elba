(declare-rel inv ( Int Int Int ))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var k Int)
(declare-var k1 Int)

(rule (inv i j k))

(rule (=> 
    (and 
        (inv i j k)
        (>= (+ i j k) 0)
        (or (and (= i1 (- i 1)) (= j1 j))
            (and (= j1 (+ j 1)) (= i1 i)))
        (= k1 (- k 2))
    )
    (inv i1 j1 k1)
  )
)
