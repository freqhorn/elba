(declare-rel inv (Int Int Int Int) )
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var tx Int)
(declare-var tx1 Int)

(rule (inv x y z tx))
(rule 
    (=>
        (and 
          (inv x y z tx)
          (>= x y)
          (<= x (+ tx z) )
          (or 
            (and 
              (= z1 (- z 1) )
              (= tx1 x)
              (= y1 y)
            )
            (and
              (= y1 (+ y 1 ) )
              (= x1 x)
              (= z1 z)
              (= tx1 tx)
            )
          )
        )  
        (inv x1 y1 z1 tx1)
    )
)
