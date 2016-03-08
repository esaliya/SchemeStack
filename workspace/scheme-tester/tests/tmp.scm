(define val-of-cbv
  (lambda (exp env)
    (pmatch exp
      [,b (guard (boolean? b)) b]
      [,n (guard (number? n)) n]
      [,x (guard (symbol? x)) (unbox (apply-env env x))]
      [(zero? ,n) (zero? (val-of-cbv n env))]
      [(sub1 ,n) (sub1 (val-of-cbv n env))]
      [(* ,n1 ,n2) (* (val-of-cbv n1 env) (val-of-cbv n2 env))]
      [(lambda (,x) ,body) (closure-cbv x body env)]
	  [(let ([,x ,e]) ,body) 
	   (let ([a (val-of-cbv e env)]) 
		(val-of-cbv body (lambda (y) (if (eqv? x y) (box a) (env y)))))]
      [(if ,test ,conseq ,alt) (if (val-of-cbv test env)
                                   (val-of-cbv conseq env)
                                   (val-of-cbv alt env))]
      [(set! ,x ,rhs) (set-box! (apply-env env x) (val-of-cbv rhs env))]
      [(begin2 ,e1 ,e2) (begin (val-of-cbv e1 env) (val-of-cbv e2 env))]
      [(random ,n) (random n)]
      [(,rator ,rand) (apply-proc (val-of-cbv rator env)
                                  (box (val-of-cbv rand env)))])))
								  
(define empty-env
  (lambda ()
    (lambda (y)
      (error 'empty-env "unbound variable ~s" y))))

(define extend-env
  (lambda (env x a)
    (lambda (y) (if (eq? x y) a (apply-env env y)))))

(define apply-env
  (lambda (env x)
    (env x)))

(define apply-proc
  (lambda (p a)
    (p a)))

;; Closure for the call-by-value 
(define closure-cbv
  (lambda (x body env)
    (lambda (a) (val-of-cbv body (extend-env env x a)))))