(declare-rel inv (Int Int))
(declare-var n0 Int)
(declare-var x0 Int)
(declare-var x1 Int)

(rule (=> (= x0 n0) (inv n0 x0)))

(rule (=> (and
        (inv n0 x0)
        (> x0 0)
        (= x1 (- x0 1))
        )
        (inv n0 x1)
))

; This C program uses a break statement to exit the loop. The if guard is used here as the loop guard.
