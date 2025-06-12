(declare-rel inv (Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var c Int)
(declare-var c1 Int)
(declare-var flag Int)
(declare-var flag1 Int)

(rule (=> (and (= flag 1) (= c 0)) (inv x y c flag)))

(rule (=>
    (and
        (inv x y c flag)
        (not (= flag 0))
        (= flag1 (ite (>= x y) 0 flag))
        (= x1 (+ x 1))
        (= c1 (+ c 1))
    )
    (inv x1 y c1 flag1)
  )
)

; Elba SEG FAULT