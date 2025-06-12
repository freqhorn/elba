(declare-rel inv (Int Int Int Int) )
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var m Int)
(declare-var m1 Int)
(declare-var n Int)
(declare-var n1 Int)

(rule 
	(=>
		(and 
			(> m 0)
			(> n m)
			(= i 0)
			(= j 0)
		)
		(inv i j m n )
	)
)
(rule 
    (=>
        (and 
          (inv i j m n )
          (< i n)
          (= m1 m)
          (= n1 n)
          (or
            (and 
              (< j m)
              (= i1 i)
              (= j1 (+ j 1) )
            )
            (and 
              (not (< j m) )
              (= j1 0)
              (= i1 (+ i 1) )
            )
          )
        )
        (inv i1 j1 m1 n1 )
    )
)
