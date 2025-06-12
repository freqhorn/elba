(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(declare-rel fail ())

(rule (inv x y z))

(rule (=> 
    (and 
        (inv x y z)
        (>= x y)
        (or
            (and (= z1 (- z 1)) (= x1 (+ x z1)) (= y1 y))
            (and (= y1 (+ y 1)) (= x1 x) (= z1 z))
        )
    )
    (inv x1 y1 z1)
  )
)

(rule (=> (and (inv x y z) (>= x y)) fail))

(query fail :print-certificate true)
