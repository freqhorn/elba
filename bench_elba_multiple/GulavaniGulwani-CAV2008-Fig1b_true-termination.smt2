(declare-rel first (Int Int Int Int))
(declare-rel second (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var i0 Int)
(declare-var i1 Int)
(declare-var N Int)
(declare-var M Int)

(rule (=> true (first x0 i0 N M)))

(rule (=> (and
        (first x0 i0 N M)
        (< x0 N)
        (= x1 (+ x0 1))
        (= i1 (+ i0 1))
        )
    (first x1 i1 N M)))

(rule (=> (first x0 i0 N M) (second x0 i0 N M)))

(rule (=> (and
        (second x0 i0 N M)
        (< x0 M)
        (= x1 (+ x0 1))
        (= i1 (+ i0 1))
        )
    (second x1 i1 N M)))

; 