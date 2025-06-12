(declare-rel inv ( Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var z Int)

(rule (=> (>= (* 2 y) z)  (inv x y z)))

(rule (=> 
    (and 
        (inv x y z)
        (>= x 0)
        (= z 1)
        (= x1 (+ x 1 (- 0 (* 2 y))))
    )
    (inv x1 y z)
  )
)
