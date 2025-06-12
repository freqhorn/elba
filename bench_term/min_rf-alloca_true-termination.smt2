(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (> x 0)
        (> y 0)
        (= z (ite (> x y) y x))
        (or (and (= y1 (+ x y)) (= x1 (- z 1)))
            (and (= x1 (+ x y)) (= y1 (- z 1))))
    )
    (inv x1 y1)
  )
)
