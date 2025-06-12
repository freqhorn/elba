(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(rule (=> (>= (* 2 y) 1)  (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (>= x 0)
        (= x1 (+ x 1 (- 0 (* 2 y))))
    )
    (inv x1 y)
  )
)
