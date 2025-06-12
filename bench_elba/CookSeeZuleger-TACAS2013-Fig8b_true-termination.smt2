(declare-rel inv (Int Int ))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var M Int)

(rule (=> true (inv x0 M)))

(rule (=> (and
        (inv x0 M)
        (not (= x0 M))
        (= x1 (ite (> x0 M) 0 (+ x0 1))))
    (inv x1 M)))


; cyclic paths not allowed..