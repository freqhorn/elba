(declare-rel inv (Int Int Int))
(declare-var id Int)
(declare-var max Int)
(declare-var tmp1 Int)
(declare-var tmp2 Int)

(rule (=> (and (<= 0 id) (< id max) (= tmp1 (+ 1 id))) (inv id max tmp1)))

(rule (=> 
    (and 
        (inv id max tmp1)
        (not (= tmp1 id))
        (= tmp2 (ite (<= tmp1 max) (+ tmp1 1) -1))
    )
    (inv id max tmp2)
  )
)
