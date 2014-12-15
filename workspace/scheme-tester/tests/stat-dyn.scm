(load "pmatch.scm")

;-------------------------------------------------------------------------
; Interpreter with both lambda and d-lambda support
;-------------------------------------------------------------------------
(define value-of
  (lambda (e env)
    (pmatch e
      [,x (guard (symbol? x)) (apply-env env x)]
      [,x (guard (boolean? x)) x]      
      [(null? ,x) (null? (value-of x))]      
      [(lambda (,x) ,body) (closure x body env)]
      [(d-lambda (,x) ,body) (d-closure x body)]
      [,n (guard (number? n)) n]
      [(* ,exp-1 ,exp-2) (* (value-of exp-1 env) (value-of exp-2 env))]
      [(let ,s ,body) (value-of body (extend-env-with-list s env))]
      [(sub1 ,exp) (sub1 (value-of exp env))]
      [(if ,con ,kt, kf) (if (value-of con env) (value-of kt env) (value-of kf env))]
      [(zero? ,exp) (zero? (value-of exp env))]      
      [(,rator ,rand) (apply-proc (value-of rator env) (value-of rand env) env)])))


;---------------------------------------------------------------------------
; Helper function to extend the environment with a list of name/value pairs
;---------------------------------------------------------------------------
(define extend-env-with-list
  (lambda (s env)
    (cond
      [(null? s) env]
      [(not (null? (cdr s))) (extend-env-with-list (cdr s) (extend-env (caar s) (value-of (cadar s) env) env))]
      [else (extend-env (caar s) (value-of (cadar s) env) env)])))


;-------------------------------------------------------------------------
; Helper functions for environment based on data structure representation
;-------------------------------------------------------------------------
(define empty-env
  (lambda ()
    `(empty-env)))

(define extend-env
  (lambda (x a env)
    `(extend-env ,x ,a ,env)))

(define apply-env
  (lambda (env y)
    (pmatch env
      [(empty-env) (error 'empty-env "unbound variable ~s" y)]
      [(extend-env ,x ,a ,env) (if (eq? y x) a (apply-env env y))])))


;----------------------------------------------------------------------
; Helper functions for procedures based on higher order representation
;----------------------------------------------------------------------
(define apply-proc
  (lambda (p a env^)
    (p a env^)))

(define closure
  (lambda (x body env)
    (lambda (a env^) (value-of body (extend-env x a env)))))
      
(define d-closure
  (lambda (x body)
    (lambda (a env^) (value-of body (extend-env x a env^)))))
  



(define map
  (lambda (f)
    (lambda (l)
      (cond
        [(null? l) '()]
        [else (cons (f (car l)) ((map f) (cdr l)))]))))

;;(let ([l '(a b c)])
;;   ((map (lambda (x) (cons x l))) l))

;;(let ([l '(a b c)])
;;  (((lambda (f)
;;      (lambda (l)
;;        (cond
;;          [(null? l) '()]
;;          [else (cons (f (car l)) ((map f) (cdr l)))]))) (lambda (x) (cons x l))) l))

(value-of '(let ([l '(a b c)])
             (((d-lambda (f)
                 (d-lambda (l)
                   (if (null? l) '()
                     (cons (f (car l)) ((map f) (cdr l)))))) (d-lambda (x) (cons x l))) l)) (empty-env))