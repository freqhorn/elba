(declare-rel inv (Int Int ) )
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule 
    (=>
        (and 
            (inv x y)
            (> (+ (* 4 x) y) 0)
            (= x1 (+ (* -2 x) (* 4 y) ) )
            (= y1 (* 4 x))
        )  
        (inv x1 y1)
    )
)
