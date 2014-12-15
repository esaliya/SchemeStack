; Parser for converting Scheme to the tagged representation that we use for
; ParentheC.

(load "pmatch.scm")

(define parse
  (lambda (expr)
    (let eval ([expr expr] [env (empty-env)])
      (pmatch expr
        [,n (guard (integer? n)) `(exp_const ,n)]
        [,v (guard (symbol? v)) `(exp_var ,(apply-env v env))]
        [(zero? ,n1) (let ((n1 (eval n1 env)))
                       `(exp_zero ,n1))]
        [(* ,n1 ,n2) (let ((n1 (eval n1 env))
                           (n2 (eval n2 env)))
                       `(exp_mult ,n1 ,n2))]
        [(sub1 ,n1) (let ((n1 (eval n1 env)))
                      `(exp_sub1 ,n1))]
        [(if ,test ,conseq ,alt)
         (let ((test (eval test env))
               (conseq (eval conseq env))
               (alt (eval alt env)))
           `(exp_if ,test ,conseq ,alt))]
        [(letcc ,body) (let ((body (eval body env)))
                         `(exp_letcc ,body))]
        [(throw ,vexp ,kexp) (let ((vexp (eval vexp env))
                                   (kexp (eval kexp env)))
                               `(exp_throw ,vexp ,kexp))]        
        [(lambda ,id* ,body)
         (let ([new-env (extend-env (if (null? id*) '(()) id*) env)])
           (let loop ([l id*])
             (cond
               [(null? l) (eval body new-env)]
               [else `(exp_lambda ,(loop (cdr l)))])))]
        [(,rator . ,rand*) (guard (list? rand*))
         (let ((rator (eval rator env))
               (rand* (map (lambda (x) (eval x env)) rand*)))
           (if (null? rand*)
               `(exp_app ,rator 0)
               (let loop ([l (reverse rand*)])
                 (cond
                   [(null? l) rator]
                   [else `(exp_app ,(loop (cdr l)) ,(car l))]))))]
        [else (error "invalid language construct ~s" expr)]))))

(define empty-env
  (lambda ()
    '()))

(define extend-env
  (lambda (ids env)
    (let loop ([ids (reverse ids)])
      (cond
        [(null? ids) env]
        [else (cons (car ids) (loop (cdr ids)))]))))

(define apply-env
  (lambda (var env)
    (cond
      [(null? env) (error "unbound variable ~s" var)]
      [(eq? var (car env)) 0]
      [else (+ 1 (apply-env var (cdr env)))])))
