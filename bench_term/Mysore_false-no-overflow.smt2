(declare-rel inv (Int Int))
(declare-var c Int)
(declare-var c1 Int)
(declare-var x Int)
(declare-var x1 Int)

(rule (=> (>= c 2) (inv c x)))

(rule (=> 
    (and 
        (inv c x)
        (>= (+ c x) 0)
        (= x1 (- x c))
        (= c1 (+ c 1))
    )
    (inv c1 x1)
  )
)
