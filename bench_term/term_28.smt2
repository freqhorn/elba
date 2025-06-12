(declare-rel inv (Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (> x y)
        (or
            (and (= x1 (- x 1)) (= y1 y))
            (and (= x1 x) (= y1 (+ y 1)))
            (and (= x1 (- x 2)) (= y1 y))
            (and (= x1 x) (= y1 (+ y 2)))
            (and (= x1 (- x 3)) (= y1 y))
            (and (= x1 x) (= y1 (+ y 3)))
            (and (= x1 (- x 4)) (= y1 y))
            (and (= x1 x) (= y1 (+ y 4)))
            (and (= x1 (- x 5)) (= y1 y))
            (and (= x1 x) (= y1 (+ y 5)))
        )
    )
    (inv x1 y1)
  )
)
