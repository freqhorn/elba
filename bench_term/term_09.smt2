(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var K Int)

(rule (=> (< x y) (inv x y K)))

(rule (=> 
    (and 
        (inv x y K)
        (not (= y K))
        (or (and (= x y)
                 (= x1 (ite (> x K) (- x 1) (+ x 1)))
                 (= y1 x1))
            (and (not (= x y))
                 (= x1 x)
                 (= y1 (- y 1))))
    )
    (inv x1 y1 K)
  )
)
