;;-----------------------
;; Saliya Ekanayake
;; sekanaya
;; Test11
;;-----------------------

;; CPS version of Fibonacci calculator
(letrec ([fib.1 (lambda (n.2 k.3)
                  (if (eq? n.2 '0) 
                      (k.3 '0)
                      (if (eq? (- n.2 '1) '0)
                          (k.3 '1)
                          (letrec ([outerK.4 (lambda (v.5)
                                               (letrec ([innerK.6 (lambda (u.7)
                                                                    (k.3 (+ v.5 u.7)))])
                                                 (fib.1 (- (- n.2 '1) '1) innerK.6)))])
                            (fib.1 (- n.2 '1) outerK.4)))))]
         [emptyK.8 (lambda (w.9) w.9)])
  (fib.1 '5 emptyK.8))
