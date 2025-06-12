(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var r Int)
(declare-var r1 Int)

(rule (=> (and (= x (- r)) (= y (- r1))) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (> x y)
        (= y1 (+ y x))
        (= x1 (+ x 1))
    )
    (inv x1 y1)
  )
)
