(set-logic HORN)
(declare-fun mc91 ( Int Int ) Bool)
(assert (forall ((n Int)) (=> (> n 100) (mc91 n (- n 10)))))
(assert (forall ((n Int) (t Int) (r Int))
    (=>
        (and
            (<= n 100)
            (mc91 (+ n 11) t)
            (mc91 t r)
        )
        (mc91 n r)
    )
))
(assert (forall ((n Int) (r Int))
    (=>
        (and
            (<= n 101)
            (not (= r 91))
            (mc91 n r)
        )
        false
    )
))
