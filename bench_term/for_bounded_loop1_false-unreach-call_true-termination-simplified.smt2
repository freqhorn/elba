(declare-rel inv (Int Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var N Int)

(declare-rel fail ())

(rule (inv 0 0 0 N))

(rule (=> 
    (and 
        (inv i x y N)
        (< i N)
        (= i1 (+ i 1))
        (= x2 (- x y))
        (= x1 (+ x2 y1))
    )
    (inv i1 x1 y1 N)
  )
)

(rule (=> (and (inv i x y N) (< i N)) fail))

(query fail :print-certificate true)
