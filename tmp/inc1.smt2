(declare-fun |loop| ( Int Int Int Int ) Bool)
(declare-fun |loop_exit| ( Int Int ) Bool)

(assert
  (forall ( (from Int) (k Int) (bound Int) )
    (=>
      (and
        (>= k 0)
        (<= k bound)
        (>= from 0)
        (<= from k)
      )
      (loop from 0 k bound)
    )
  )
)

(assert
  (forall ( (i Int) (j Int) (k Int) (bound Int) )
    (=>
      (and
        (loop i j k bound)
        (< i k)
      )
      (loop (+ i 1) (+ j 1) k bound)
    )
  )
)

(assert
  (forall ( (i Int) (j Int) (k Int) (bound Int) )
    (=>
      (and
        (loop i j k bound)
        (>= i k)
      )
      (loop_exit j bound)
    )
  )
)

(assert
  (forall ( (i Int) (j Int) (k Int) (bound Int) )
    (=>
      (and
        (loop_exit j bound)
      )
      (<= j bound)
    )
  )
)

(check-sat)

(get-model)
(exit)
