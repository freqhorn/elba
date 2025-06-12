(declare-rel inv (Int Int Int Int) )
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var n Int)
(declare-var n1 Int)
(declare-var b Int)
(declare-var b1 Int)

(rule (inv x y n b ) )
(rule 
  (=>
    (and
			(inv x y n b)
			(>= x 0)
			(<= 0 y)
			(<= y n)
			(or 
				(and 
					(= b 0)
					(= y1 (+ y 1) )
          (= x1 x)
					(or (= b1 1) (= b1 b))
				)
				(and 
					(not (= b 0) )
					(= y1 (- y 1) )
					(or 
						(and 
							(= x1 (- x 1))
							(= b1 0)
						)
            (and
              (= x1 x)
              (= b1 b)
            )
					)
				)
			)
    )
    (inv x1 y1 n b1)
  )
)
