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


(define rember*evenXhowmanyeven
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*evenXhowmanyeven (car l))) ))
                        (rember*evenXhowmanyeven (cdr l)))]
      [(odd? (car l)) ((star_store (lambda (d) (unit_store (cons (car l) d))))
                       (rember*evenXhowmanyeven (cdr l)))]      
                                  
      [else ((star_store (lambda (__) (rember*evenXhowmanyeven (cdr l))))
             (lambda (s) `(__ . ,(add1 s))))])))

((rember*evenXhowmanyeven '(2 3 1 4 7)) 0)


(define rember*noneXhowmanyeven
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*noneXhowmanyeven (car l))) ))
                        (rember*noneXhowmanyeven (cdr l)))]
      [(odd? (car l)) ((star_store (lambda (d) (unit_store (cons (car l) d))))
                       (rember*noneXhowmanyeven (cdr l)))]        
                                  
      [else ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons d a))))
                                      (rember*noneXhowmanyeven (cdr l)))))
             (lambda (s) `(,(car l) . ,(add1 s))))])))


(define rember*evenXhowmanyodd
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*evenXhowmanyodd (car l))) ))
                        (rember*evenXhowmanyodd (cdr l)))]
      
      [(odd? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons d a))))
                                                (rember*evenXhowmanyodd (cdr l)))))
                       (lambda (s) `(,(car l) . ,(add1 s))))]      
      
                                  
      [else ((star_store (lambda (d) (unit_store d)))
             (rember*evenXhowmanyodd (cdr l)))])))

; We could either change odd? to even? as in here or swap the RHS of odd? with else
(define rember*oddXhowmanyeven
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*oddXhowmanyeven (car l))) ))
                        (rember*oddXhowmanyeven (cdr l)))]
      
      [(even? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons d a))))
                                                (rember*oddXhowmanyeven (cdr l)))))
                       (lambda (s) `(,(car l) . ,(add1 s))))]      
      
                                  
      [else ((star_store (lambda (d) (unit_store d)))
             (rember*oddXhowmanyeven (cdr l)))])))


(define rember*evenXsumofeven
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*evenXsumofeven (car l))) ))
                        (rember*evenXsumofeven (cdr l)))]
      
      [(even? (car l)) ((star_store (lambda (__) (rember*evenXsumofeven (cdr l))))
                        (lambda (s) `(__ . ,(+ (car l) s))))]
      
                                  
      [else ((star_store (lambda (d) (unit_store (cons (car l) d))))
             (rember*evenXsumofeven (cdr l)))])))


(define rember*evenXdifferenceofoddsandevens
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*evenXdifferenceofoddsandevens (car l))) ))
                        (rember*evenXdifferenceofoddsandevens (cdr l)))]
      
      [(even? (car l)) ((star_store (lambda (__) (rember*evenXdifferenceofoddsandevens (cdr l))))
                        (lambda (s) `(__ . ,(- s (car l)))))]
      
                                  
      [else ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons d a))))
                                      (rember*evenXdifferenceofoddsandevens (cdr l)))))
             (lambda (s) `(,(car l) . ,(+ s (car l)))))])))


(define zeroXfact
  (lambda (n)
    (cond 
      [(zero? n) (unit_store 0)]
      [else ((star_store (lambda (__) (zeroXfact (sub1 n))))
             (lambda (s) `(__ . ,(* s n))))])))


(define binaryXdecimal
  (lambda (l)
    (cond
      [(null? l) ((star_store (lambda (__) (unit_store '())))
                  (lambda (s)
                    `(__ . 0)))]
                              
      [else ((star_store (lambda (a) ((star_store (lambda (d) ((star_store (lambda (__) (unit_store (cons (car l) d))))
                                                                (lambda (s)
                                                                  (cond
                                                                    [(eq? 1 (car l)) `(__ . ,(+ s a))]
                                                                    [else `(__ . ,s)])))))
                                       (binaryXdecimal (cdr l)))))
              (lambda (s)
                (cond
                  [(eq? 0 s) `(1 . 1)]
                  [else `(,(* 2 s) . ,(* 2 s))])))])))


(define power
  (lambda (x n)
    (cond
      [(zero? n) 1]
      [(= n 1) x]
      [(odd? n) (* x (power x (sub1 n)))]
      [(even? n) (let ((nhalf (/ n 2)))
                   (let ((y (power x nhalf)))
                     (* y y)))])))

                           
(define powerXhowmanymults
  (lambda (x n)
    (cond
      [(zero? n) (unit_store 1)]
      [(= n 1) (unit_store x)]
      [(odd? n) ((star_store (lambda (__) ((star_store (lambda (d) (unit_store (* x d))))
                                           (powerXhowmanymults x (sub1 n)))))
                 (lambda (s)
                   `(__ . ,(add1 s))))]
      [(even? n) ((star_store (lambda (__) ((star_store (lambda (d) (unit_store (* d d))))
                                            (powerXhowmanymults x (/ n 2)))))
                  (lambda (s)
                    `(__ . ,(add1 s))))])))


(define howmanymultsXpower
  (lambda (x n)
    (cond
      [(zero? n) ((star_store (lambda (d) (unit_store d)))
                  (lambda (s) 
                    `(0 . 1)))]
      [(= n 1) ((star_store (lambda (d) (unit_store d)))
                  (lambda (s) 
                    `(0 . ,x)))]
      [(odd? n) ((star_store (lambda (d)
                               ((star_store (lambda (__) (unit_store (+ d 1))))
                                (lambda (s)
                                  `(__ . ,(* x s))))))
                 (howmanymultsXpower x (sub1 n)))]
      
      [(even? n) ((star_store (lambda (d)
                                ((star_store (lambda (__) (unit_store (+ d 1))))
                                 (lambda (s)
                                   `(__ . ,(* s s))))))
                  (howmanymultsXpower x (/ n 2)))])))

; Brainteaser
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

(define callcc
  (lambda (g)
    (lambda (k)
      (let ((k-as-proc (lambda (a) (lambda (k_ignored) (k a)))))
        (let ((Ma (g k-as-proc)))
          (Ma k))))))


(define value-of-cps
  (lambda (expr env)
    (pmatch expr
      [,n (guard (or (number? n) (boolean? n))) (unitcps n)]      
      [,x (guard (symbol? x)) (apply-env-cps env x)]
      [(* ,x1 ,x2) ((starcps (lambda (v) ((starcps (lambda (w) (unitcps (* v w))))
                                         (value-of-cps x2 env))))
                    (value-of-cps x1 env))]       
      [(sub1 ,x) ((starcps (lambda (v) (unitcps (sub1 v))))
                  (value-of-cps x env))]       
      [(zero? ,x) ((starcps (lambda (v) (unitcps (zero? v))))
                   (value-of-cps x env))]       
      [(if ,test ,conseq ,alt) ((starcps (lambda (b) (if b
                                                       (value-of-cps conseq env)
                                                       (value-of-cps alt env))))
                                (value-of-cps test env))]

      [(letcc ,k-id ,body) (callcc (lambda (out) 
                                      (value-of-cps body (extend-env k-id out env))))]

      [(throw ,v-exp ,k-exp) ((starcps (lambda (c) ((starcps (lambda (v) (c v)))
                                                    (value-of-cps v-exp env))))
                              (value-of-cps k-exp env))]       

      [(lambda (,id) ,body) (unitcps (closure id body env))]
      [(,rator ,rand) ((starcps (lambda (v) ((starcps (lambda (w) (apply-proc-cps w v)))
                                             (value-of-cps rator env))))
                       (value-of-cps rand env))])))
       

;--------------------------------------------------------------------------------------
; Constructors for environments and procedures based on data-structural representation
;--------------------------------------------------------------------------------------
(define empty-env
  (lambda ()
    `(mt-env)))

(define extend-env
 (lambda (x a env)
   `(ext-env ,x ,a ,env)))

(define closure
  (lambda (id body env)
    `(clos ,id ,body ,env)))

;--------------------------------------------------------------------------------------
; Monadifed using CPS Monad: observers for environments and procedures based on data-structural 
; representation
;--------------------------------------------------------------------------------------
(define apply-env-cps
 (lambda (env y)
   (pmatch env
     [(mt-env) (error 'empty env "unbound variable ~s : discarding continuation" y)] ;let's keep it for the moment
     [(ext-env ,x ,a ,env) (if (eq? x y) (unitcps a) (apply-env-cps env y))])))

(define apply-proc-cps
  (lambda (p a)
    (pmatch p
      [(clos ,id ,body ,env) (value-of-cps body (extend-env id a env))])))


       
       
       








      