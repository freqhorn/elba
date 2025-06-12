(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var j Int)
(declare-var j1 Int)

(rule (=> (and (> y 0) (> x y)) (inv x y j)))

(rule (=>
    (and
        (inv x y j)
        (> x 0) (> y 0)
        (= x1 (ite (= (mod j 2) 0) (- x 1) x))
        (= y1 (- y 1))
        (= j1 (+ j 1))
    )
    (inv x1 y1 j1)
  )
)
