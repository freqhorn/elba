(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)

(rule (inv 15))

(rule (=>
    (and
        (inv x)
        (> x 5)
        (= x1 (- x 1))
    )
    (inv x1)
  )
)
