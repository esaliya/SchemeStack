(load "pmatch.scm")

(define valof
  (lambda (e env)
    (pmatch e
      [,x (guard (symbol? x)) (env x)]
      [,x (guard (number? x)) x]
      [(lambda (,x) ,body) (closure body x env)]
      [(,rator ,rand) (apply-proc (valof rator env) (valof rand env))])))

;;(define closure
;;  (lambda (body x env)
;;    (lambda (a) (valof body (lambda (y) (if (eq? x y) a (env y)))))))

;;(define apply-proc
;;  (lambda (p a)
;;    ((valof rator env) (valof rand env))))

(define closure
  (lambda (body x env)
    `(closure ,body ,x ,env)))

(define apply-proc
  (lambda (p a)
    (pmatch p
      [(closure ,body ,x ,env) (valof body (lambda (y) (if (eq? x y) a (env y))))])))
              
              
          