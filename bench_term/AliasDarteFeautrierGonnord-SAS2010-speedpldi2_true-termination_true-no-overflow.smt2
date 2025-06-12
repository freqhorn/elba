(declare-rel inv (Int Int Int Int) )
(declare-var m Int)
(declare-var m1 Int)
(declare-var n Int)
(declare-var n1 Int)
(declare-var v1 Int)
(declare-var v11 Int)
(declare-var v2 Int)
(declare-var v21 Int)

(rule 
	(=> 
		(and 
			(>= n 0)
			(> m 0)
			(= v1 n)
			(= v2 0)
		)
		(inv m n v1 v2 )
	)
)

(rule 
    (=>
        (and 
          (inv m n v1 v2 )
          (> v1 0)
          (= m1 m)
          (= n1 n)
          (or 
            (and 
              (< v2 m)
              (= v21 (+ v2 1) )
              (= v11 (- v1 1) ) 
            )
            (and 
              (not (< v2 m) )
              (= v21 0)
              (= v11 v1)
            )
          )
        )
        (inv m1 n1 v11 v21 )
    )
)

