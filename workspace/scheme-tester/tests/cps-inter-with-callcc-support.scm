(define value-of-cps
  (lambda (expr env k)
    (pmatch expr
      [,n (guard (or (number? n) (boolean? n))) (k n)]      
      [,x (guard (symbol? x)) (apply-env-cps env x k)]
      [(* ,x1 ,x2) (value-of-cps x1 env (lambda (v) (value-of-cps x2 env (lambda (w) (k (* v w))))))]
      [(sub1 ,x) (value-of-cps x env (lambda (v) (k (sub1 v))))]
      [(zero? ,x) (value-of-cps x env (lambda (v) (k (zero? v))))]
      [(if ,test ,conseq ,alt) (value-of-cps test env (lambda (v) (if v 
                                                                (value-of-cps conseq env k)
                                                                (value-of-cps alt env k))))]
;;    Original letcc line in the direct style interpreter
;;    [(letcc ,k-id ,body) (call/cc (lambda (k)
;;                                    (value-of body (extend-env k-id k env))))]
;;    The continuation we grab from call/cc is essentially the future waiting for
;;    the call/cc to finish. Now, in this cps version we get the particular future
;;    as k, so we don't want to invoke call/cc to grab it. Therefore, the line above
;;    becomes,
      [(letcc ,k-id ,body) (value-of-cps body (extend-env k-id k env) k)]
;;    originally, the second continuation would be something like (lambda (v) (c v))
;;    but this gave us the opportunity to do a eta transformation 
      [(throw ,v-exp ,k-exp) (value-of-cps k-exp env (lambda (c) (value-of-cps v-exp env c)))]
      [(call/cc ,rator)
;;    (k (closure id body env)) is a tail call since closure is a simple thing which returns
;;    instantly, to be more clear think of this as (k `(clos ,id ,body, env))
      [(lambda (,id) ,body) (k (closure id body env))]
      [(,rator ,rand) (value-of-cps rand env (lambda (v) (value-of-cps rator env (lambda (w) (apply-proc-cps w v k)))))])))


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
; CPSed observers for environments and procedures based on data-structural 
; representation
;--------------------------------------------------------------------------------------
(define apply-env-cps
 (lambda (env y k)
   (pmatch env
     [(mt-env) (error 'empty env "unbound variable ~s : discarding continuation" y)]
     [(ext-env ,x ,a ,env) (if (eq? x y) (k a) (apply-env-cps env y k))])))

(define apply-proc-cps
  (lambda (p a k)
    (pmatch p
;;    Once again, the (extend-env ...) too returns instantly, thus, value-of-cps
;;    call is a tail call
      [(clos ,id ,body ,env) (value-of-cps body (extend-env id a env) k)])))