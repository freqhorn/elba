(declare-rel inv (Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var N Int)

(rule (=> (not (= z 0)) (inv x y z N)))

(rule (=> 
    (and 
        (inv x y z N)
        (<= x N)
        (>= (+ x y) 0)
        (= x1 (- (* 2 x) y))
        (= y1 z)
        (= z1 (* -2 z))
    )
    (inv x1 y1 z1 N)
  )
)
