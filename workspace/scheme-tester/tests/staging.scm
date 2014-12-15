(define val-of
  (lambda (exp env)
    (pmatch exp
      [,x (guard (symbol? x)) (env x)]
      [(lambda (,x) ,body) (lambda (a) (val-of body (lambda (y) (if (eq? x y) a (env y)))))]
      [(,rator ,rand) ((val-of rator env) (val-of rand env))])))

; Now, let's split our env into s-env and d-env
; s-env -> (x y z)
; d-env -> (5 4 3)

; Assuming a flat list for s-env, we can define the index of a symbol in s-env as,
(define index
  (lambda (x l)
    (- (length l) (length (memq x l)))))

(define val-of
  (lambda (exp s-env)
    (lambda (d-env)
      (pmatch exp
        [,x (guard (symbol? x)) (let ([i (index x s-env)])
                                  (list-ref d-env i))]
        [,n (guard (number? n)) n]
        [(lambda (,x) ,body) (lambda (a) ((val-of body (cons x s-env)) (cons a d-env)))]
        [(,rator ,rand) (((val-of rator s-env) d-env) ((val-of rand s-env) d-env))]))))

(define empty-s-env '())
(define empty-d-env '())

; ((val-of '((lambda (y) ((lambda (x) x) y)) 10) empty-s-env) empty-d-env)

; Great! it works. Now, let's push our d-env to RHS of pmatches

(define val-of
  (lambda (exp s-env)
    (pmatch exp
      [,x (guard (symbol? x)) (lambda (d-env)
                                (let ([i (index x s-env)])
                                  (list-ref d-env i)))]
      [,n (guard (number? n)) (lambda (d-env) n)]
      [(lambda (,x) ,body) (lambda (d-env)
                             (lambda (a) ((val-of body (cons x s-env)) (cons a d-env))))]
      [(,rator ,rand) (lambda (d-env)
                        (((val-of rator s-env) d-env) ((val-of rand s-env) d-env)))])))

; Great! it works too. Now let's do whatever we can when we can, i.e. push out things which are not
; dependent on d-env

(define val-of
  (trace-lambda valof (exp s-env)
    (pmatch exp
      [,x (guard (symbol? x)) (let ([i (index x s-env)])
                                (lambda (d-env)
                                  (list-ref d-env i)))]
      [,n (guard (number? n)) (lambda (d-env) n)]
      [(lambda (,x) ,body) (let ([c-body (val-of body (cons x s-env))])
                             (lambda (d-env)
                               (lambda (a) (c-body (cons a d-env)))))]
      [(,rator ,rand) (let ([c-rator (val-of rator s-env)] [c-rand (val-of rand s-env)])
                        (lambda (d-env)
                          ((c-rator d-env) (c-rand d-env))))])))

;;(let ([c-code (val-of '10 empty-s-env)])
;;  (c-code empty-d-env))
;; 

;;(let ([c-code (val-of '((lambda (y) ((lambda (x) x) y)) 10) empty-s-env)])
;;  (printf "\nI will NOT see pmatch again\n")  
;;  (c-code empty-d-env))

;;(let ([c-code (val-of '((lambda (x) x) 10) empty-s-env)])
;;    (c-code empty-d-env))