(declare-rel inv (Int ))
(declare-var i0 Int)
(declare-var i1 Int)

(rule (=> true (inv i0)))

(rule (=> (and
        (inv i0)
        (<= i0 2147483647)
        (= i1 (+ i0 1)))
    (inv i1)))
