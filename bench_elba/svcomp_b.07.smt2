(declare-rel inv (Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var c Int)
(declare-var c1 Int)
(declare-var z Int)

(rule (=> (= c 0) (inv x y z c)))

(rule (=>
    (and
        (inv x y z c)
        (and (> x z) (> y z))
        (= x1 (- x 1))
        (= y1 (- y 1))
        (= c1 (+ c 1))
    )
    (inv x1 y1 z c1)
  )
)

; Elba SOLVED