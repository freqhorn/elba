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
        (not (= x y))
        (= x1 (ite (> x y) x (+ x 1)))
        (= y1 (ite (> x y) (+ y 1) y))
        (= c1 (+ c 1))
    )
    (inv x1 y1 c1)
  )
)

; Elba SOLVED