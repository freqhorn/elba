(declare-rel inv (Int Int ) )
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)

(rule (inv a b))

(rule 
    (=>
        (and 
            (inv a b)
            (> a 0)
            (= a1 (+ (* 3 a) (* -4 b) ))
            (= b1 (+ (* 4 a) (* 3 b) ))
        )  
        (inv a1 b1)
    )
)
