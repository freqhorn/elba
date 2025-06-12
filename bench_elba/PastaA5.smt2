(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=>
    (and
        (inv x y)
        (>= x (+ y 1))
        (= y1 (+ y 1))
    )
    (inv x y1)
  )
)

; Elba SOLVED