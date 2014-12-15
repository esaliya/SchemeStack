;;----------------------------------
;; B521 - Assignment 9
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    0002560797
;; Email: sekanaya@indiana.edu
;;----------------------------------

;----------------------------------------------------------------
; CPSed interpreter
; ---------------------------------------------------------------
; expression constructors
(define-union exp
  (const n)
  (var v)
  (if test conseq alt)
  (mult rand1 rand2)
  (sub1 rand)
  (zero rand)
  (letcc body)
  (throw vexp kexp)
  (lambda body)
  (app rator rand))

(define value-of
  (lambda (expr env k)
    (union-case expr exp
      [(const n) (k n)]
      [(var v) (apply-env env v k)]
      [(if test conseq alt) (value-of test env (lambda (b)
                                                 (if b
                                                   (value-of conseq env k)
                                                   (value-of alt env k))))]
      [(mult rand1 rand2) (value-of rand1 env (lambda (v) (value-of rand2 env (lambda (u) (k (* v u))))))]
      [(sub1 rand) (value-of rand env (lambda (v) (k (- v 1))))]
      [(zero rand) (value-of rand env (lambda (v) (k (zero? v))))]
      [(letcc body) (value-of body (envr_extend k env) k)]
      [(throw vexp kexp) (value-of kexp env (lambda (c) (value-of vexp env c)))]
      [(lambda body) (k (clos_closure body env))]
      [(app rator rand) (value-of rator env (lambda (p) (value-of rand env (lambda (a) (apply-proc p a k)))))])))

(define-union envr
  (empty)
  (extend arg env))

(define apply-env
  (lambda (env num k)
    (union-case env envr
      [(empty) (error 'pc "unbound variable")]
      [(extend arg env)
       (if (zero? num)
         (k arg)
         (apply-env env (sub1 num) k))])))

(define-union clos
  (closure code env))

(define apply-proc
  (lambda (c a k)
    (union-case c clos
      [(closure code env)
       (value-of code (envr_extend a env) k)])))

(define main
  (lambda ()
    (value-of (exp_app
                        (exp_lambda
                          (exp_app
                            (exp_app (exp_var 0) (exp_var 0))
                            (exp_const 5)))
                        (exp_lambda
                          (exp_lambda
                            (exp_if (exp_zero (exp_var 0))
                                    (exp_const 1)
                                    (exp_mult (exp_var 0)
                                              (exp_app
                                                (exp_app (exp_var 1) (exp_var 1))
                                                (exp_sub1 (exp_var 0))))))))
                     (envr_empty) (lambda (v) v))))
    
