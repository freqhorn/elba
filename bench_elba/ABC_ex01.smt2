(declare-rel inv (Int Int Int))
(declare-var a0 Int)
(declare-var a1 Int)
(declare-var b0 Int)
(declare-var b1 Int)
(declare-var i0 Int)
(declare-var i1 Int)

(rule (=> (= i0 a0) (inv a0 b0 i0)))

(rule (=> (and
        (inv a0 b0 i0)
        (< i0 b0)
        (= i1 (+ i0 1))
        )
        (inv a0 b0 i1)
))
