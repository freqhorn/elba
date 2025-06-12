(declare-rel inv (Int ))
(declare-var x Int)
(declare-var x1 Int)

(rule (inv 0))

(rule (=> 
    (and 
        (inv x )
        (< x 1000)
        (= x1 (ite (= x 7777) x (+ x 1)))
    )
    (inv x1)
  )
)
