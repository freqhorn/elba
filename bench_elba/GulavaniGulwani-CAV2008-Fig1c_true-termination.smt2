(declare-rel inv (Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var i0 Int)
(declare-var i1 Int)
(declare-var n Int)

(rule (=> true (inv x0 i0 n)))

(rule (=> (and
        (inv x0 i0 n)
        (< x0 n)
        (= i1 (+ i0 1))
        (= x1 (+ x0 1))
        )
    (inv x1 i1 n)))
