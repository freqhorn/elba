(declare-rel inv ( Int Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)

(rule (inv i j a b))

(rule (=> 
    (and 
        (inv i j a b)
        (= (+ i j a b) 0)
        (or (and (= i1 (- i 1)) (= j1 j))
            (and (= j1 (+ j 1)) (= i1 i)))
        (or (and (= a1 (- a 2)) (= b1 b))
            (and (= b1 (+ b 2)) (= a1 a)))
    )
    (inv i1 j1 a1 b1)
  )
)
