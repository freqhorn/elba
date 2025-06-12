(declare-rel inv (Int Int Int Int Int))
(declare-var m0 Int)
(declare-var n0 Int)
(declare-var dir Int)
(declare-var fwd Int)
(declare-var i0 Int)
(declare-var i1 Int)

(rule (=> (and (> m0 0) (> n0 m0) (= i0 m0)) (inv m0 n0 dir fwd i0)))

(rule (=> (and
        (inv m0 n0 dir fwd i0)
        (and (< 0 i0) (< i0 n0))
        (= i1 (ite (= dir fwd) (+ i0 1) (- i0 1)))
        )
        (inv m0 n0 dir fwd i1)
))

;Bound: max(m, n-m)
