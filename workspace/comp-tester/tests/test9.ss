;;-----------------------
;; Saliya Ekanayake
;; sekanaya
;; Test7
;;-----------------------

;; Really bad fibonacci calculator that does
;; calculations on the heap :)
(letrec ([fib$1 (lambda (p.2 n.3)
                 (if (< n.3 2)
                     (mref p.2 8)
                     (begin
                       (let ([t.4 (mref p.2 8)])
                         (begin
                           (mset! p.2 8 (+ (mref p.2 0) t.4))
                           (mset! p.2 0 t.4)))
                       (fib$1 p.2 (- n.3 1)))))])
  (let ([x.1 (alloc 16)])
    (begin
      (mset! x.1 0 0)
      (mset! x.1 8 1)
      (fib$1 x.1 5))))
