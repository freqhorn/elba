(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=>
    (and
        (inv x y)
        (not (= x y))
        (= x1 (ite (> x y) x (+ x 1)))
        (= y1 (ite (> x y) (+ y 1) y))
    )
    (inv x1 y1)
  )
)

; Elba SOLVED