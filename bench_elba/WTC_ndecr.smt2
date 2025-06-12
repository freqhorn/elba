(declare-rel inv (Int Int))
(declare-var n0 Int)
(declare-var i0 Int)
(declare-var i1 Int)

(rule (=> (= i0 (- n0 1)) (inv n0 i0)))

(rule (=> (and
        (inv n0 i0)
        (> i0 1)
        (= i1 (- i0 1))
        )
        (inv n0 i1)
))
