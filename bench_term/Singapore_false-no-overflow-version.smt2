(declare-rel inv (Int Int) )
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule 
    (=>
        (<= (+ x y) 0 )
        (inv x y)
    )
)
(rule 
    (=>
        (and 
            (inv x y)
            (> x 0)
            (= x1 (+ x y 2))
            (= y1 (- y 1))
        )  
        (inv x1 y1)
    )
)
