(declare-rel inv (Int Int ))
(declare-var i0 Int)
(declare-var i1 Int)
(declare-var n Int)

(rule (=> (= i0 (- n 1)) (inv i0 n)))

(rule (=> (and
        (inv i0 n)
        (> i0 1)
        (= i1 (- i0 1)))
    (inv i1 n)))
