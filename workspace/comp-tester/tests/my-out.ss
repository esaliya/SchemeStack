; my optimize-source output for original introduce-procedure-primitives out
(letrec ([vector-scale!$0 (lambda (vect.1 scale.2)
                            (let ([size.3 (vector-length vect.1)])
                              (vector-scale!$12 size.3 vect.1 scale.2)))]
         [vector-sum$13 (lambda (vect.7)
                          (vector-sum$14 (vector-length vect.7) vect.7))])
  (let ([vect.11 (make-vector '5)])
    (begin
      (vector-set! vect.11 '0 '123)
      (vector-set! vect.11 '1 '10)
      (vector-set! vect.11 '2 '7)
      (vector-set! vect.11 '3 '12)
      (vector-set! vect.11 '4 '57)
      (vector-scale!$0 vect.11 '10)
      (vector-sum$13 vect.11))))