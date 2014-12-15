(define empty-k-exit
  (lambda (exit)
    `(empty-k ,exit)))

; original fact
;;(define fact
;;  (lambda (n)
;;    (if (= n 0) 1 (* n (fact (sub1 n))))))

; CPSed fact
;;(define fact
;;  (lambda (n k)
;;    (lambda ()
;;      (if (= n 0)
;;        (k 1)
;;        (fact (sub1 n) (lambda(v) (k (* n v))))))))

(define trampoline
  (lambda (th)
    (trampoline (th))))

; something is wrong with the following code

;;(define fact
;;  (lambda (n k)
;;    (lambda ()
;;      (if (= n 0)
;;        (apply k k 1)
;;        (fact (sub1 n) (create-k k n))))))

;;(define create-k
;;  (lambda (k n)
;;    `(create-k ,k ,n)))

;;(define apply-k
;;  (lambda (k v)
;;    (lambda()
;;      (pmatch k
;;        [(emtpy-k ,exit) (exit v)]
;;        [(create-k ,k ,n) (apply-k k (* n v))]))))

;;(call/cc (lambda (exit)
;;           (trampoline (lambda () (fact 4 (empty-k-exit exit)))))) 

;;(trampoline (lambda () 
;;              (call/cc (lambda (exit)
;;                         (fact 0 (empty-k-exit exit)))))) <-- is this correct, I think wrong

;;(define first
;;  (lambda (th1 th2)
;;    (call/cc 
;;      (lambda (exit)
        
               
      