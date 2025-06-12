(declare-rel inv (Int Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var tx Int)
(declare-var tx1 Int)
(declare-var ty Int)
(declare-var ty1 Int)
(declare-var N Int)

(declare-rel fail ())

(rule (=> (>= (+ x y) 0) (inv x y tx ty N)))

(rule (=> 
    (and 
        (inv x y tx ty N)
        (<= x N)
        (>= x (+ (* 2 tx) y))
        (>= y (+ ty 1))
        (>= x (+ tx 1))
        (or
            (and (= tx1 x) (= ty1 y))
            (and (= tx1 x) (= ty1 ty) (= y1 y))
        )
    )
    (inv x1 y1 tx1 ty1 N)
  )
)

(rule (=> (and (inv x y tx ty N)
    (<= x N)
    (>= x (+ (* 2 tx) y))
    (>= y (+ ty 1))
    (>= x (+ tx 1))
) fail))

(query fail :print-certificate true)
