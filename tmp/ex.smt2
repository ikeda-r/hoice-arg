(declare-fun |p| ( Int ) Bool)

(assert
  (forall ( (i Int) )
    (=>
      true
      (p 0)
    )
  )
)

(assert
  (forall ( (i Int) )
    (=>
      (and
        (p i)
        (< i 10)
      )
      (p (+ i 1))
    )
  )
)

(assert
  (forall ( (i Int) )
    (=>
      (and
        (p i)
        (> i 15)
      )
      false
    )
  )
)

(check-sat)

(get-model)
(exit)
