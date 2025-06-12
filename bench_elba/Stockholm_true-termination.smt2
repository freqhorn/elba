(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var a Int)
(declare-var b Int)

(rule (=> true (inv x a b)))

(rule (=>
    (and
        (inv x a b)
        (>= x 0) 
;        (= a b)
        (= x1 (- x 1))
    )
    (inv x1 a b)
  )
)
