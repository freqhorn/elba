(declare-rel inv ( Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (inv x y z))

(rule (=> 
    (and 
        (inv x y z)
        (< x y) (= y1 y)
        (or (and (> z x) (= x1 (+ x 1)) (= z1 z))
            (and (<= z x) (= z1 (+ z 1)) (= x1 x)))
    )
    (inv x1 y1 z1)
  )
)
