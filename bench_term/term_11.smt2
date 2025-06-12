(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var K Int)

(rule (inv x y K))

(rule (=> 
    (and 
        (inv x y K)
        (or (not (= x K)) (not (= y K)))
        (= x1 (ite (> x K) (- x 1) (ite (< x K) (+ x 1) x)))
        (= y1 (ite (> y K) (- y 1) (ite (< y K) (+ y 1) y)))
    )
    (inv x1 y1 K)
  )
)
