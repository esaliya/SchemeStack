(define value-of
  (lambda (exp env)
    (pmatch exp
      [,n (guard (or (number? n) (boolean? n))) n]
      [,x (guard (symbol? x)) (apply-env env x)]
      [(* ,x1 ,x2) (* (value-of x1 env) (value-of x2 env))]
      [(+ ,x1 ,x2) (+ (value-of x1 env) (value-of x2 env))]
      [(sub1 ,x) (sub1 (value-of x env))]
      [(zero? ,x) (zero? (value-of x env))]
      [(if ,test ,conseq ,alt) (if (value-of test env)
                                   (value-of conseq env)
                                   (value-of alt env))]
      [(call/cc ,p) (call/cc (lambda (k) (apply-proc (value-of p env) k)))]
      [(lambda (,id) ,body) (closure id body env)]
      [(,rator ,rand) (apply-proc (value-of rator env) (value-of rand env))])))

; I will go ahead with data structures for the helpers
(define empty-env
  (lambda ()
    `(--mt-env)))

(define extend-env
 (lambda (x a env)
   `(--ext-env ,x ,a ,env)))

(define apply-env
 (lambda (env y)
   (pmatch env
     [(--mt-env) (error 'inside empty env "unbound variable ~s" y)]
     [(--ext-env ,x ,a ,env) (if (eq? x y) a (apply-env env y))])))

(define closure
  (lambda (id body env)
    `(--clos ,id ,body ,env)))

(define apply-proc
  (lambda (p a)
    (pmatch p
      [(--clos ,id ,body ,env) (value-of body (extend-env id a env))]
      ; This is cuz we can't differentiate between applying a continuation to an argument
      ; (i.e. (k a))
      ; vs applying a procedure to an argument. If we had our helpers based on procedures
      ; then apply-proc would work seamlessly with both cases as we know that system
      ; continuations are presented as higher order functions. The two methods below show
      ; that this works :).
      [,x (x a)])))

;;(define closure
;;  (lambda (id body env)
;;    (lambda (y) (value-of body (extend-env id y env)))))

;;(define apply-proc
;;  (lambda (p a)
;;    (p a)))


(trace empty-env)
(trace extend-env)
(trace apply-env)
(trace closure)
(trace apply-proc)
(trace value-of)
(trace *)
(trace +)
(trace call/cc)