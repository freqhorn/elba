(declare-rel inv (Int Int Int Int) )
(declare-var x Int)
(declare-var x1 Int)
(declare-var n Int)
(declare-var b Int)
(declare-var t Int)

(rule (=> (= t (ite (>= b 1) 1 -1)) (inv x n b t)))
(rule 
    (=>
        (and 
            (inv x n b t)
            (<= x n)
            (= x1 (+ x (ite (>= b 1) t (- t))))
        )
        (inv x1 n b t)
    )
)
