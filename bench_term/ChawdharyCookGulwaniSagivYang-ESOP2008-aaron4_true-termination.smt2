(declare-rel inv (Int Int Int Int Int Int) )
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var k Int)
(declare-var k1 Int)
(declare-var an Int)
(declare-var bn Int)
(declare-var tk Int)
(declare-var tk1 Int)

(rule (inv i j k an bn tk))
(rule 
    (=>
        (and 
            (inv i j k an bn tk)
            (or (and (>= an i) (>= bn j)) (and (>= an i) (<= bn j)) (and (<= an i) (>= bn j)))
            (>= k (+ tk 1))
            (or
                (and (>= an i) (>= bn j) (or (and (= j1 (+ j k)) (= tk1 k) (= i1 i)) (and (= i1 (+ i 1)) (= j1 j) (= k1 k) (= tk1 tk))))
                (and (not (and (>= an i) (>= bn j))) (>= an i) (<= bn j) (= i1 (+ i 1)) (= j1 j) (= k1 k) (= tk1 tk))
                (and (not (and (>= an i) (>= bn j))) (not (and (>= an i) (<= bn j))) (<= an i) (>= bn j) (= j1 (+ j k)) (= tk1 k) (= i1 i))
            )
        )
        (inv i1 j1 k1 an bn tk1)
    )
)
