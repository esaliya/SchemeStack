(define fib
  (lambda (n k)
    (cond
      [(eq? n 0) (lambda () (k 1))]
      [(eq? (sub1 n) 0) (lambda () (k 1))]
      [else (lambda () 
              (fib (sub1 n) 
                   (lambda (v) 
                     (lambda () 
                       (fib (sub1 (sub1 n)) 
                            (lambda (w) 
                              (lambda () 
                                (k (+ v w)))))))))])))

(define tramp
  (lambda (th)
    (tramp (th))))