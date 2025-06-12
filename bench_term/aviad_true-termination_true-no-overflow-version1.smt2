(declare-rel inv (Int))
(declare-var a Int)
(declare-var a1 Int)

(declare-rel fail ())

(rule (inv a))

(rule (=> 
    (and 
        (inv a)
        (> a 1)
        (= a1
            (ite (= (mod a 2) 0)
                (div a 2)
                    (ite (= (mod a 3) 0)
                    (div a 3)
                    (+ a 1))))
    )
    (inv a1)
  )
)

(rule (=> (and (inv a) (> a 1)) fail))

(query fail :print-certificate true)
