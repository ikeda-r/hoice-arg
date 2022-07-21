(declare-fun |loop| ( Int Int Int ) Bool)
(declare-fun |loop_exit| ( Int Int ) Bool)
(declare-fun |loop2| ( Int Int Int ) Bool)
(declare-fun |loop2_exit| ( Int Int ) Bool)

(assert
  (forall ( (n Int) )
    (=>
      (and
        (>= n 0)
      )
      (loop 0 n 0)
    )
  )
)

(assert
  (forall ( (i Int) (n Int) (acc Int) )
    (=>
      (and
        (loop i n acc)
        (<= i n)
      )
      (loop (+ i 1) n (+ 1 acc))
    )
  )
)

(assert
  (forall ( (i Int) (n Int) (acc Int) )
    (=>
      (and
        (loop i n acc)
        (> i n)
      )
      (loop_exit n acc)
    )
  )
)

(assert
  (forall ( (n Int) (acc Int) )
    (=>
      (and
        (loop_exit n acc)
      )
      (<= n acc)
    )
  )
)

(assert
  (forall ( (n Int) (acc Int) )
    (=>
      (and
        (loop_exit n acc)
      )
      (loop2 0 n acc)
    )
  )
)

(assert
  (forall ( (i Int) (n Int) (acc Int) )
    (=>
      (and
        (loop2 i n acc)
        (<= i n)
      )
      (loop2 (+ i 1) n (+ 2 acc))
    )
  )
)

(assert
  (forall ( (i Int) (n Int) (acc Int) )
    (=>
      (and
        (loop2 i n acc)
        (> i n)
      )
      (loop2_exit n acc)
    )
  )
)

(assert
  (forall ( (n Int) (acc Int) )
    (=>
      (and
        (loop2_exit n acc)
      )
      (<= (* 3 n) acc)
    )
  )
)

(check-sat)

(get-model)
(exit)
