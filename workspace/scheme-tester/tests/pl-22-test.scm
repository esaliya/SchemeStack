;--------------------------------------------------------------------------------------------------------
; This is the direct style using a separate variable to mimic the store
; We can get to this even with sotre monad by doing a number of beta and eta substitutions
(define remberevenXhowmanyeven
  (lambda (l)
    (lambda (s)
      (cond
        [(null? l) `(() . ,s)]
        [(odd? (car l)) (let ([p ((remberevenXhowmanyeven (cdr l)) s)])
                          `(,(cons (car l) (car p)) . ,(cdr p)))]
        [else (let ([p ((remberevenXhowmanyeven (cdr l)) s)])
                `(,(car p) . ,(add1 (cdr p))))]))))
;--------------------------------------------------------------------------------------------------------
; Now for the continuation stuff

; We could have done the above without any store assuming the initial value of s to be 0
(define remberevenXhowmanyeven
  (lambda (l)
    (cond
      [(null? l) `(() . ,0)]
      [(odd? (car l)) (let ([p (remberevenXhowmanyeven (cdr l))])
                        `(,(cons (car l) (car p)) . ,(cdr p)))]
      [else (let ([p (remberevenXhowmanyeven (cdr l))])
              `(,(car p) . ,(add1 (cdr p))))])))

; Let's CPS this
(define remberevenXhowmanyeven
  (lambda (l k)
    (cond
      [(null? l) (k `(() . ,0))]
      [(odd? (car l)) (remberevenXhowmanyeven (cdr l) (lambda (p) (k `(,(cons (car l) (car p)) . ,(cdr p)))))]        
      [else (remberevenXhowmanyeven (cdr l) (lambda (p) (k `(,(car p) . ,(add1 (cdr p))))))])))  

; Let's use CPS Monad :)

(define unitcps
  (lambda (a)
    (lambda (k) ; ⇐= This lambda is a Ma.
      (k a))))

(define starcps
  (lambda (f)
    (lambda (Ma)
      (lambda (k) ; ⇐= This lambda is a Ma.                 
        (let ((k^ (lambda (a)
                    (let ((Ma^ (f a)))
                      (Ma^ k )))))
          (Ma k^))))))

(define remberevenXhowmanyeven
  (lambda (l)
    (cond
      [(null? l) (unitcps `(() . ,0))]
      [(odd? (car l)) ((starcps (lambda (p) (unitcps `(,(cons (car l) (car p)) . ,(cdr p)))))
                       (remberevenXhowmanyeven (cdr l)))]
      [else ((starcps (lambda (p) (unitcps `(,(car p) . ,(add1 (cdr p))))))
             (remberevenXhowmanyeven (cdr l)))])))

(define rember*evensXcountevens
  (lambda (l)
    (cond
       ((null? l) (unitcps `(() . 0)))
       ((pair? (car l))
         ((starcps (lambda (pa)
                     ((starcps (lambda (pd) (unitcps `(,(cons (car pa) (car pd)) . ,(+ (cdr pa) (cdr pd))))))
                      (rember*evensXcountevens (cdr l)))))
          (rember*evensXcountevens (car l))))
       ((or (null? (car l)) (odd? (car l)))
         ((starcps (lambda (p) (unitcps `(,(cons (car l) (car p)) . ,(cdr p)))))
          (rember*evensXcountevens (cdr l))))
       (else ((starcps (lambda (p) (unitcps `(,(car p) . ,(add1 (cdr p))))))
               (rember*evensXcountevens (cdr l)))))))

       


