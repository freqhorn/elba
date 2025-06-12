(declare-rel inv (Int Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)
(declare-var d1 Int)
(declare-var x Int)
(declare-var x1 Int)

(rule (inv 0 0 0))

(rule (=> 
    (and 
        (inv j x d)
        (< d 98)
        (= d1 (+ (mod j 50) (mod x 50)))
        (= j1 (+ j 1))
        (= x1 (+ x 1))
    )
    (inv j1 x1 d1)
  )
)
