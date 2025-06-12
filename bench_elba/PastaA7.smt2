(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (inv x y z))

(rule (=>
    (and
        (inv x y z)
        (and (> x y) (> x z))
        (= y1 (+ y 1))
        (= z1 (+ z 1))
    )
    (inv x y1 z1)
  )
)

; Elba SOLVED