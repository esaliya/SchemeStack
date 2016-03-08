;;(define M
;;  (lambda (f)
;;    (lambda (ls)
;;      (cond
;;        ((null? ls) '())
;;        (else (cons (f (car ls)) ((M f) (cdr ls))))))))

;;>((M add1) '(1 2 3))


(define M
  (lambda (f k)
    (k (lambda (ls c)
         (cond
           ((null? ls) (c '()))
           (else (M f (lambda (g) (g (cdr ls) (lambda (l) (c (cons (f (car ls)) l))))))))))))

;;>(M add1 (lambda (g) (g '(1 2 3) (lambda (x) x)))) 
    

;; This is not correct since there is still non-tail calls, see ((M f ...) ...).
;; 
;;(define M
;;  (lambda (f k)
;;    (lambda (ls)
;;      (cond
;;        ((null? ls) (k '()))
;;        (else ((M f (lambda (v) (k (cons (f (car ls)) v)))) (cdr ls)))))))

;;((M add1 (lambda (x) x)) '(1 2 3))