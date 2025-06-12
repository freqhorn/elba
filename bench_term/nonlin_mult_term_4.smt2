(declare-rel inv (Int Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)
(declare-var b Int)

(declare-rel fail ())

(rule (=> (and (> d 1) (> b 1) (< d b)) (inv 1 1 d b)))

(rule (=> 
    (and 
        (inv i j d b)
        (>= i j)
        (= i1 (* i d))
        (= j1 (* j b))
    )
    (inv i1 j1 d b)
  )
)

(rule (=> (and (inv i j d b) (>= i j)) fail))

(query fail :print-certificate true)
