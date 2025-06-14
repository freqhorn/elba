(declare-rel inv (Int Int Int Int))
(declare-var i0 Int)
(declare-var i1 Int)
(declare-var j0 Int)
(declare-var j1 Int)
(declare-var k0 Int)
(declare-var k1 Int)
(declare-var tmp0 Int)
(declare-var tmp1 Int)

(rule (=> true (inv i0 j0 k0 tmp0)))

(rule (=> (and
        (inv i0 j0 k0 tmp0)
        (and (<= i0 100) (<= j0 k0))
        (= tmp1 i0)
        (= i1 j0)
        (= j1 (+ 1 tmp1))
        (= k1 (- k0 1))
        )
        (inv i1 j1 k1 tmp1)
))
