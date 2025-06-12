(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(rule (=> true (inv i j)))

(rule (=>
    (and
        (inv i j)
        (> (* i j) 0)
        (= i1 (- i 1))
        (= j1 (- j 1))
    )
    (inv i1 j1)
  )
)

; gh = i or gh = j if i or j > 0
; else gh = 0
; Nonterm if both i and j < 0