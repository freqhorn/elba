(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)

(declare-rel fail ())

(rule (inv x))

(rule (=>
    (and
        (inv x)
        (> x 0)
        (= x1 (- x 1))
    )
    (inv x1)
  )
)

