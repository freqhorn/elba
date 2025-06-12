(declare-rel inv (Int Int))
(declare-var b0 Int)
(declare-var x0 Int)
(declare-var x1 Int)

(rule (=> true (inv b0 x0)))

(rule (=> (and
        (inv b0 x0)
        (and (< 0 x0) (< x0 255))
        (= x1 (ite (= b0 0) (- x0 1) (+ x0 1)))
        )
        (inv b0 x1)
))

; The if statement has been reversed from the C program for simplicity in translating.
