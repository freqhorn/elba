(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

; requires --transform 4

(rule (=> (and (> y 1) (= z 0)) (inv x y z)))

(rule (=>
  (and
    (inv x y z)
    (> x 0)
    (= x1 (- x y))
    (= y1 (- y z))
    (= z1 (ite (= z 0) 13 (ite (= z 13) -20 (ite (= z -20) 7 0)))))
  (inv x1 y1 z1)
  )
)
