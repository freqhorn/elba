(declare-rel inv (Int Int Int Int) )
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var tx Int)
(declare-var tx1 Int)

(rule (=>
		(and 
			(<= -1073741823 tx) 
			(<= tx 1073741823)
			(<= -1073741823 x) 
			(<= x 1073741823)
			(<= -1073741823 z) 
			(<= z 1073741823)
			(<= y 1073741823)
		)
		(inv x y z tx))
	  )
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
              (<= -1073741823 x1)
              (<= x1 1073741823)
            )
            (and
              (= y1 (+ y 1 ) )
              (= x1 x)
              (= tx1 tx)
              (= z1 z)
            )
          )
        )
        (inv x1 y1 z1 tx1)
    )
)
