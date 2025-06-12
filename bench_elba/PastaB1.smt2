(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)

(rule (inv x y))

(rule (=>
    (and
        (inv x y)
        (> x y)
        (= x1 (- x 1))
    )
    (inv x1 y)
  )
)

; Elba SOLVED