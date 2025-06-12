(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(rule (=> (>= (* 5 y) 1)  (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (>= x 0)
        (= x1 (+ x 3 (- 0 (* 4 y))))
    )
    (inv x1 y)
  )
)
