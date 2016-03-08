(define succeed (== #f #f))
(define fail (== #f #t))

(define anyo
  (lambda (g)
    (conde
      [g]
      [(anyo g)])))

(define alwayso (anyo succeed))
(define nevero (anyo fail))