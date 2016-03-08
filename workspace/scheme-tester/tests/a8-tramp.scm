;;(define fact
;;  (lambda (n)
;;    (if (= n 0) 1 (* n (fact (sub1 n))))))

(define fact-cps
  (lambda (n k)
    (if (= n 0)
      (k 1)
      (fact-cps (sub1 n) (lambda (v) (k (* n v)))))))

(define empty-k
  (lambda ()
    (lambda (v) v)))

(define fact-driver
  (lambda (n)
    (fact-cps n (empty-k))))

(define fact-tramp
  (lambda (n k)
    (lambda ()
      (if (= n 0)
        (fact-apply-k k 1)
        (fact-tramp (sub1 n) (fact-k k n))))))

(define fact-k
  (lambda (k n)
    `(fact-k ,k ,n)))

(define fact-exit-k
  (lambda ()
    `(exit-k)))

(define fact-apply-k
  (lambda (k v)
    (pmatch k
      [(exit-k) (*exit* v)] ; grab the exit continuation from the register and throw v into that
      [(fact-k ,k ,n) (fact-apply-k k (* n v))])))

;;(define tramp
;;  (lambda (th)
;;    (tramp (th))))

;;(define empty-k-exit
;;  (lambda (exit)
;;    (lambda (v)
;;      (exit v))))

;;(define fact-tramp-driver
;;  (lambda (n)
;;    (call/cc
;;      (lambda (exit)
;;        (tramp (lambda () (fact-tramp n (empty-k-exit exit))))))))

(define *exit* '*)

(define fact
  (lambda (n)
    (lambda () (fact-tramp n (fact-exit-k)))))

(define trampoline
  (lambda (th1 th2)
    (trampoline (th2) th1)))

(define first
  (lambda (thnk1 thnk2)
    (call/cc
      (lambda (exit)
        (begin
          (set! *exit* exit)
          (trampoline thnk1 thnk2))))))
          
                        
          
        



; our call would be like (f t1 t2)

;;(define f
;;  (lambda (th1 th2)
;;    (th1)))
    

;;(define fact
;;  (lambda (n)
;;    (lambda () (fact-tramp n (empty-k)))))

;;(define t1 (lambda () (fact 5)))
;;(define t2 (lambda () (fact 2)))

;;(define first
;;  (lambda (th1 th2)
;;    (call/cc
;;      (lambda (exit)
;;        (letrec ([f (lambda (thnk1 thnk2)
;;                      
    
    