(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (=> (and
    (<= -1073741823 x)
    (<= x 1073741823)
    (<= -1073741823 y)
    (<= y 1073741823)
  ) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (or (>= x 0) (>= y 0))
        (= x1 (- y 1))
        (= y1 (- x 1))
    )
    (inv x1 y1)
  )
)
