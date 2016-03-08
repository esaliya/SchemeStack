
((let ([fib (lambda (fib)
              (lambda (n)
                (cond
                  [(eq? n 0) 1]
                  [(eq? n 1) 1]
                  [else (+ ((fib fib) (sub1 n)) ((fib fib) (sub1 (sub1 n))))])))])
   (fib fib)) 4)

(((lambda (fib)
   (fib fib)) (lambda (fib)
                (lambda (n)
                  (cond
                    [(eq? n 0) 1]
                    [(eq? n 1) 1]
                    [else (+ ((fib fib) (sub1 n)) ((fib fib) (sub1 (sub1 n))))])))) 4)

((let ([fac (lambda (fac)
             (lambda (n)
               (if (zero? n) 
                 1
                 (* ((fac fac) (sub1 n)) n))))])
  (fac fac)) 5)

(((lambda (fac)
   (fac fac)) (lambda (fac)
                (lambda (n)
                  (if (zero? n) 1                
                    (* ((fac fac) (sub1 n)) n))))) 5)

((letrec ([fac (lambda (n)
                (if (zero? n) 
                  1
                  (* (fac (sub1 n)) n)))])
   fac) 5)
                
