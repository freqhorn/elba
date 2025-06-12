(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (= c 0) (inv x y c)))

(rule (=>
    (and
        (inv x y c)
        (> x y)
        (= x1 (- x 1))
        (= c1 (+ c 1))
    )
    (inv x1 y c1)
  )
)

; Elba SOLVED