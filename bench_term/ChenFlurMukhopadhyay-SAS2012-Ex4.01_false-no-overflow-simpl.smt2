(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var N Int)

(declare-rel fail ())

(rule (inv x y N))

(rule (=> 
    (and 
        (inv x y N)
        (>= (+ x y) 0)
        (<= x N)
        (= x1 (+ (* 2 x) y))
        (= y1 (+ y 1))
    )
    (inv x1 y1 N)
  )
)

(rule (=> (and (inv x y N) (>= (+ x y) 0) (<= x N)) fail))

(query fail :print-certificate true)
