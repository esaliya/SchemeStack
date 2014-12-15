(define fac
  (lambda (x)
    (cond
      [(zero? x) 1]
      [else (* x (fac (sub1 x)))])))

(define Yv
  (lambda (f)
    (lambda (x) ;; I will call this the inovker
      (((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x))))) x))))
;;                     |----- pop corn -----|


(define f
  (lambda (p) ;; The pop corn :)
    (lambda (x) ;; The invoker. It'll in fact, be the one provided to Yv
      (lambda (n) ;; The number
        (if (zero? n) 
            1
            (* n ((p x) (sub1 n))))))))

(define facyv
  (lambda (n)
    (((Yv f) (lambda (x) x)) n)))

;; To make you dizzy let's put all together


((((lambda (f)
     (lambda (x) ;; I will call this the inovker
       (((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x))))) x)))
   (lambda (p) ;; The pop corn :)
     (lambda (x) ;; The invoker. It'll in fact, be the one provided to Yv
       (lambda (n) ;; The number
         (if (zero? n)
             1
             (* n ((p x) (sub1 n))))))))
  (lambda (x) x))
 5)
    