(declare-rel inv ( Int Int Int))
(declare-var N Int)
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (< N 536870912) (< x 536870912)
               (< y 536870912) (>= x -1073741824)
               (>= (+ x y) 0)) (inv N x y)))

(rule (=> 
    (and 
        (inv N x y)
        (<= x N)
        (or (and (= x1 (+ (* 2 x) y)) (= y1 (+ y 1)))
            (and (= x1 (+ x 1)) (= y1 y))
        )
    )
    (inv N x1 y1)
  )
)

(rule (=> (and (inv N x y) (<= x N)) fail))

(query fail :print-certificate true)
