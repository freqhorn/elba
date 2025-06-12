(declare-rel inv ( Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var z Int)

(rule (=> (and (> (* 10 y) z) (< z 10))  (inv x y z)))

(rule (=> 
    (and 
        (inv x y z)
        (>= x 0)
        (= x1 (+ x (* -10 y) z))
    )
    (inv x1 y z)
  )
)
