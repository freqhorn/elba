(declare-rel inv ( Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var k Int)
(declare-var k1 Int)

(declare-rel fail ())

(rule (inv i j k))

(rule (=> 
    (and 
        (inv i j k)
        (<= i 100)
        (<= j k)
        (> k -1073741824) ; some large number
        (= i1 j)
        (= j1 (+ i 1))
        (= k1 (- k 1))
    )
    (inv  i1 j1 k1)
  )
)

(rule (=> (and (inv  i j k)
  (<= i 100)
  (<= j k)
  (> k -1073741824))
fail))

(query fail :print-certificate true)
