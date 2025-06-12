(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)

(rule (inv x))

(rule (=> 
    (and 
        (inv x )
        (<= x 100)
        (or
            (= x1 (+ (* -2 x) 2))
            (= x1 (- (* -3 x) 2))
        )
    )
    (inv x1 ))
)
