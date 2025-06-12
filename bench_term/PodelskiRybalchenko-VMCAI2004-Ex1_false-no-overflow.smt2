(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var nondetNat Int)
(declare-var nondetPos Int)

(rule (inv i j))

(rule (=> 
    (and 
        (inv i j)
        (>= (- i j) 1)
        (>= nondetNat 0)
        (> nondetPos 0)
        (= i1 (- i nondetNat))
        (= j1 (+ j nondetPos))
    )
    (inv i1 j1)
  )
)
