(define binary-to-decimal
  (lambda (s)
    (letrec ([f (lambda (s m)
                  (cond
                    [(null? s) 0]
                    [else (+ (* m (car s)) (f (cdr s) (* 2 m)))]))])
      (f s 1))))

