(declare-rel inv (Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var oldx Int)
(declare-var oldx1 Int)

(declare-rel err ())

(rule (inv x oldx))

(rule
  (=> (and (inv x oldx)
        (> x 0) 
        (< x 100)
        (>= x (+ (* 2 oldx ) 10))
        (= oldx1 x)
      )
  (inv x1 oldx1))
)

(rule (=> 
        (and (inv x oldx )
          (> x 0) 
          (< x 100)
          (>= x (+ (* 2 oldx ) 10))
        )
        err
      )
)
(query err)
