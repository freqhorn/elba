(declare-rel inv (Int Int) )
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

; requires --solver freqhorn

(rule 
	(=> (and
			(<= -1073741823 y)
			(<= y 1073741823)
			(<= z 1073741823)
		)
		(inv y z)
	)
)
(rule 
  (=>
    (and
			(inv y z )
			(>= z 0)
			(= y1 (- y 1) )
      (or
			(and 
				(>= y1 0)
				(<= z1 1073741823)
			)
			(and 
				(not (>= y1 0))
				(= z1 (- z 1) )
			))
    )
    (inv y1 z1)
  )
)
