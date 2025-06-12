(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var r0 Int)
(declare-var r1 Int)
(declare-var i0 Int)
(declare-var i1 Int)
(declare-var N Int)

(rule (=> (and (= N 10) (= x0 0) (= y0 0) (= i0 0)) (inv N x0 y0 i0)))

(rule (=> (and
        (inv N x0 y0 i0)
        (< i0 N)
        (= i1 (+ i0 1))
        (ite (= r0 0) (and (= y1 y0) (= x1 (+ x0 1))) 
            (ite (= r0 1) (and (= y1 y0) (= x1 (- x0 1))) 
                (ite (= r0 2) (and (= x1 x0) (= y1 (+ y0 1))) 
                    (ite (= r0 3) (and (= x1 x0) (= y1 (- y0 1))) 
                        (and (= x1 x0) (= y1 y0))))))
        )
    (inv N x1 y1 i1)))


; Cyclic path, but the bound is simply 10.