(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)

(declare-rel fail ())

(rule (=> (= x 0) (inv x)))

(rule (=>
    (and
        (inv x)
        (< x 1000)
        (= x1 (+ x 1))
    )
    (inv x1)
  )
)
