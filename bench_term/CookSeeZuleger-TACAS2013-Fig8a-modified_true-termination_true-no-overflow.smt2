(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var K Int)

(declare-rel fail ())

(rule (inv x K))

(rule (=> 
    (and 
        (inv x K)
        (not (= x K))
        (= x1 (ite (> x K) (- x 1) (+ x 1)))
    )
    (inv x1 K)
  )
)

(rule (=> (and (inv x K) (not (= x K))) fail))

(query fail :print-certificate true)
