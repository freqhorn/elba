(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var N Int)

(rule (inv 0 1 N))

(rule (=> 
    (and 
        (inv x y N)
        (< x N)
        (or
            (and (= y 1) (= y1 0) (= z 5))
            (and (= y 0) (= y1 1) (= z -3))
            (and (= y 1) (= y1 0) (= z 7))
            (and (= y 0) (= y1 1) (= z -2))
            (and (= z 1) (= y1 y))
        )
        (= x1 (+ x z))
    )
    (inv x1 y1 N)
  )
)
