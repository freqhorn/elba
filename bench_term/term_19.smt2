(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)

(declare-rel fail ())

(rule (=> (>= x 10) (inv x)))

(rule (=> 
    (and 
        (inv x)
        (not (= x 10))
        (= x1 (ite (= (mod x 5) 1) (+ x 1) (- x 2)))
    )
    (inv x1)
  )
)

(rule (=> (and (inv x) (not (= x 10))) fail))

(query fail :print-certificate true)
