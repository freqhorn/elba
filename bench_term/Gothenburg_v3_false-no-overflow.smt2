(declare-rel inv (Int Int Int Int) )
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (=> (= a b) (inv a b x y)))
(rule 
  (=>
    (and
      (inv a b x y )
      (or 
        (>= x 0) 
        (>= y 0)
      )
      (= a1 b)
      (= b1 a)
      (= x1 (- (+ x a) (+ b 1) ) )
      (= y1 (- (+ y b) (+ a 1) ) )
    )
    (inv a1 b1 x1 y1)
  )
)
