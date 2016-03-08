;;(define recur-ncr
;;  (trace-lambda ncr (n r)
;;    (cond
;;      [(zero? r) 1]
;;      [(and (zero? n) (> r 0)) 0]
;;      [else (+ (recur-ncr (sub1 n) (sub1 r)) (recur-ncr (sub1 n) r))])))

;;(define recur-k-ncr
;;  (lambda (n r k)
;;    (cond
;;      [(zero? r) (begin
;;                   (printf "recur-k: r==0 => n: ~s  r: ~s\n" n r)
;;                   (k 1))]
;;      [(and (zero? n) (> r 0)) (begin
;;                                 (printf "recur-k: n==0 => n: ~s  r: ~s\n" n r)
;;                                 (k 0))]
;;      [else (recur-k-ncr (sub1 n) (sub1 r) (lambda (v) (recur-k-ncr (sub1 n) r (lambda (w) (k (+ v w))))))])))

(define insertf
  (lambda (ls x)
    (cond
      [(null? ls) '()]
      [else (cons (cons x (car ls)) (insertf (cdr ls) x))])))

(define n->ls
  (lambda (n)
    (if (zero? n) '() (if (eq? 1 n) '(1) (cons n (n->ls (sub1 n)))))))

(define ls->ls*
  (lambda (ls)
    (if (null? ls)
        '()
        (cons (list (car ls)) (ls->ls* (cdr ls))))))

(define ncr
  (lambda (n r)
    (letrec ([lsncr (lambda (ls r)
                      (cond
                        [(null? ls) '()]
                        [(eq? r 1) (ls->ls* ls)]
                        [else (append (insertf (lsncr (cdr ls) (sub1 r)) (car ls))
                                      (lsncr (cdr ls) r)))])])
      (lsncr (n->ls n) r))))
                      
                        
                      
                      
              
        