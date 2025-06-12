(declare-rel inv (Int Int Int) )
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var n Int)

(rule (inv n j n ) )
(rule 
    (=>
        (and 
          (inv i j n)
          (> i 0)
          (or 
            (and 
              (> j 0)
              (= j1 (- j 1) )
              (= i1 i)
            )
            (and 
              (not (> j 0) )
              (= i1 (- i 1) )
              (= j1 n )
            )
          )
        )
        (inv i1 j1 n)
    )
)
