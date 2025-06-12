(declare-rel inv (Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var N Int)

(declare-rel fail ())

(rule (inv x y z N))

(rule (=> 
    (and 
        (inv x y z N)
        (>= (+ x y) 0)
        (<= x N)
        (= x1 (+ (* 2 x) y))
        (= y1 z)
        (= z1 (+ z 1))
    )
    (inv x1 y1 z1 N)
  )
)

(rule (=> (and (inv x y z N) (>= (+ x y) 0) (<= x N)) fail))

(query fail :print-certificate true)
