(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (= c 0) (inv x y c)))

(rule (=>
    (and
        (inv x y c)
        (and (> x 0) (> y 0))
        (= x1 (- x 1))
        (= y1 (- y 1))
        (= c1 (+ c 1))
    )
    (inv x1 y1 c1)
  )
)

; Elba SOLVED