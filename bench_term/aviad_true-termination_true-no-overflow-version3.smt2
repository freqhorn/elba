(declare-rel inv (Int))
(declare-var a Int)
(declare-var a1 Int)

; spacer stucks

(rule (inv a))

(rule (=> 
    (and 
        (inv a)
        (> a 1)
        (= a1 (ite (= (mod a 10) 0) (div a 10) (- a 1)))
    )
    (inv a1)
  )
)
