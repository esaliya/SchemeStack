; Definitions of Store Monad

(define unit_store
  (lambda (a)
    (lambda (s)     ;; <-------------------- this lambda is a Ma
      `(,a . ,s))))

(define star_store
  (lambda (f)
    (lambda (Ma)
      (lambda (s)   ;; <-------------------- this lambda is a Ma
        (let ([p (Ma s)])
          (let ([new-a (car p)] [new-s (cdr p)])
            (let ([new-Ma (f new-a)])
              (new-Ma new-s))))))))

(define rembereXmaxseq
  (lambda (l)
    (cond
      [(null? l) (unit_store '())]
      [(even? (car l)) ((star_store (lambda (__) (rembereXmaxseq (cdr l))))
                        (lambda (s)
                          `(__ . ,(let ([n (add1 (cdr s))])
                                     (if (> n (car s))
                                       (cons n n)
                                       (cons (car s) n))))))]
      [else ((star_store (lambda (__) ((star_store (lambda (p) (unit_store (cons (car l) p))))
                                       (rembereXmaxseq (cdr l)))))
             (lambda (s)
               `(__ . ,(cons (car s) 0))))])))
               