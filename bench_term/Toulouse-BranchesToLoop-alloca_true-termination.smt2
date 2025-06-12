(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (=> (or (= x 1) (= x -1)) (inv x y z)))

(rule (=> 
    (and 
        (inv x y z)
        (< y 100)
        (< z 100)
        (= y1 (+ y x))
        (= z1 (- z x))
    )
    (inv x y1 z1)
  )
)
