(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=>
    (and
        (inv x y)
        (or (> x 0) (> y 0))
        (= x1 (- x 1))
        (= y1 (- y 1))
    )
    (inv x1 y1)
  )
)

;(= gh_0
;  (ite (and (> ST_0 0) (> ST_1 (- 1)) (< (+ ST_0 (- ST_1)) 0))
;    ST_1
;    (ite (and (> ST_1 (- 1)) (< (+ ST_0 (- ST_1)) 0))
;      ST_1
;      (ite (and (> ST_1 0) (> ST_0 (- 1)) (< (+ (- ST_0) ST_1) 0))
;        ST_0
;        (ite (and (> ST_0 (- 1)) (< (+ (- ST_0) ST_1) 0))
;          ST_0
;          (ite (and (> ST_1 (- 1)) (= (+ ST_0 (- ST_1)) 0))
;            ST_1
;            0)
;)))))
