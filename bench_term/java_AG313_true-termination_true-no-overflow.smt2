(declare-rel inv ( Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel fail ())

(rule (=> (and (= i 0) (not (= x 0)))  (inv x y i)))

(rule (=> 
    (and 
        (inv x y i)
        (> x 0)
        (> y 0)
        (= i1 (+ i 1))
        (= x1 (- (- x 1) (- y 1)))
    )
    (inv x1 y i1)
  )
)

(rule (=> (and (inv x y i) (> x 0) (> y 0)) fail))

(query fail :print-certificate true)
