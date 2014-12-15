; RIP wrt continuations

(define-union exp
  (const n)
  (var v)
  (if test conseq alt)
  (mult rand1 rand2)
  (sub1 rand)
  (zero rand)
  (letcc body)
  (throw vexp kexp)
  (let vexp body)
  (lambda body)
  (app rator rand))

(define value-of
  (lambda (expr env k)
    (union-case expr exp
      [(const n) (apply-k k n)]
      [(var v) (apply-env env v k)]
      [(if test conseq alt) (value-of test env (kont_if-k conseq alt env k))]
      [(mult rand1 rand2) (value-of rand1 env (kont_mult-k1 rand2 env k))]
      [(sub1 rand) (value-of rand env (kont_sub1-k k))]
      [(zero rand) (value-of rand env (kont_zero?-k k))]
      [(letcc body) (value-of body (envr_extend k env) k)]
      [(throw vexp kexp) (value-of kexp env (kont_c-k vexp env))]
      [(let vexp body) (value-of vexp env (kont_let-k body env k))]
      [(lambda body) (apply-k k (clos_closure body env))]
      [(app rator rand) (value-of rator env (kont_proc-k rand env k))])))

(define-union envr
  (empty)
  (extend arg env))

(define apply-env
  (lambda (env num k)
    (union-case env envr
      [(empty) (errorf 'env "unbound variable")]
      [(extend arg env)
       (if (zero? num)
           (apply-k k arg)
           (apply-env env (sub1 num) k))])))

(define-union clos
  (closure code env))

(define apply-proc
  (lambda (c a k)
    (union-case c clos
      [(closure code env)
       (value-of code (envr_extend a env) k)])))

(define-union kont
  (empty-k)
  (mult-k1 rand2 env k)
  (mult-k2 w k)
  (sub1-k k)
  (zero?-k k)
  (if-k conseq alt env k)
  (c-k vexp env)
  (let-k body env k)
  (proc-k rand env k)
  (arg-k proc k))

;----------------------RIP helpers---------------------------
(define apply-k
  (lambda (k v)
    (union-case k kont
      [(empty-k) v]
      [(mult-k1 rand2 env k) (value-of rand2 env (kont_mult-k2 v k))]
      [(mult-k2 w k) (apply-k k (* w v))]
      [(sub1-k k) (apply-k k (sub1 v))]
      [(zero?-k k) (apply-k k (zero? v))]
      [(if-k conseq alt env k) (if v (value-of conseq env k) (value-of alt env k))]
      [(c-k vexp env) (value-of vexp env v)]
      [(let-k body env k) (value-of body (envr_extend v env) k)]
      [(proc-k rand env k) (value-of rand env (kont_arg-k v k))]
      [(arg-k proc k) (apply-proc proc v k)])))

;----------------------tests-----------------------------------
; Factorial of 5...should be 120.
(pretty-print
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
           (envr_empty)
           (kont_empty-k)))

; Test of letcc and throw...should evaluate to 24.
(pretty-print
 (value-of (exp_mult (exp_const 2)
                     (exp_letcc
                      (exp_mult (exp_const 5)
                                (exp_throw (exp_mult (exp_const 2) (exp_const 6))
                                           (exp_var 0)))))
           (envr_empty)
           (kont_empty-k)))

;; (let ([fact (lambda (f)                                                      
;;               (lambda (n)                                                    
;;                 (if (zero? n)                                                
;;                     1                                                        
;;                     (* n ((f f) (sub1 n))))))])                              
;;   ((fact fact) 5))                                                           

(pretty-print
 (value-of (exp_let
            (exp_lambda
             (exp_lambda
              (exp_if
               (exp_zero (exp_var 0))
               (exp_const 1)
               (exp_mult
                (exp_var 0)
                (exp_app
                 (exp_app (exp_var 1) (exp_var 1))
                 (exp_sub1 (exp_var 0)))))))
            (exp_app (exp_app (exp_var 0) (exp_var 0)) (exp_const 5)))
           (envr_empty)
           (kont_empty-k)))
