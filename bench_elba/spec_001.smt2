(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)

;(declare-rel fail ())

(rule (inv x))

(rule (=>
    (and
        (inv x)
        (> x 500)
        (= x1 (- x 1))
    )
    (inv x1)
  )
)

;(rule (=> (and (inv x) (not (> x 5)) ) fail))

;(query fail :print-certificate true)