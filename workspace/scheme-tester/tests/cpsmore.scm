(define empty-s
  (lambda ()
    '()))
 
;;(define extend-s
;;  (lambda (x v s)
;;    (cons `(,x . ,v) s)))
;; 
;;(define unify
;;  (lambda (v w s)
;;    (let ([v (walk v s)])
;;      (let ([w (walk w s)])
;;        (cond
;;          [(eq? v w) s]
;;          [(symbol? v) (extend-s v w s)]
;;          [(symbol? w) (extend-s w v s)]
;;          [(and (pair? v) (pair? w))
;;           (let ((s (unify (car v) (car w) s)))
;;             (cond
;;               [s (unify (cdr v) (cdr w) s)]
;;               [else #f]))]
;;          [(equal? v w) s]
;;          [else #f])))))

(define empty-k
  (lambda ()
    (lambda (x) x)))

(define extend-s-cps
  (lambda (x v s k)
    (k (cons `(,x . ,v) s))))

(define unify-cps
  (lambda (v w s k)
    (walk-cps v s (lambda (v)
                    (walk-cps w s (lambda (w)
                                    (cond
                                      [(eq? v w) (k s)]
                                      [(symbol? v) (extend-s-cps v w s k)]
                                      [(symbol? w) (extend-s-cps w v s k)]
                                      [(and (pair? v) (pair? w))
                                       (unify-cps (car v) (car w) s (lambda (s)
                                                                      (cond
                                                                        [s (unify (cdr v) (cdr w) s k)]
                                                                        [else (k #f)])))]
                                      [(equal? v w) (k s)]
                                      [else (k #f)])))))))
                    
     
     
     
     
(define walk-cps
  (lambda (v ls k)
    (cond
      [(symbol? v) (let ([p (assq v ls)])
                     (cond
                       [p (walk-cps (cdr p) ls k)]
                       [else (k v)]))]
      [else (k v)])))