;;----------------------------------
;; B521 - Assignment 9
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    0002560797
;; Email: sekanaya@indiana.edu
;;----------------------------------

;----------------------------------------------------------------
; R.I., w.r.t. continuations, CPSed interpreter
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
      [(const n) (apply-k k n)]
      [(var v) (apply-env env v k)]
      [(if test conseq alt) (value-of test env (kt_if_k conseq alt env k))]
      [(mult rand1 rand2) (value-of rand1 env (kt_mul1_k rand2 env k))]
      [(sub1 rand) (value-of rand env (kt_sub_k k))]
      [(zero rand) (value-of rand env (kt_zero_k k))]
      [(letcc body) (value-of body (envr_extend k env) k)]
      [(throw vexp kexp) (value-of kexp env (kt_throw_k vexp env))]
      [(lambda body) (apply-k k (clos_closure body env))]
      [(app rator rand) (value-of rator env (kt_proc_k rand env k))])))

(define-union kt
  (empty_k)
  (if_k conseq alt env k)
  (mul1_k rand2 env k)
  (mul2_k w k)
  (sub_k k)
  (zero_k k)
  (throw_k vexp env)
  (proc_k rand env k)
  (arg_k p k))
   
(define apply-k
  (lambda (k^ v)
    (union-case k^ kt
      [(empty_k) v]
      [(if_k conseq alt env k) (if v
                                 (value-of conseq env k)
                                 (value-of alt env k))]
      [(mul1_k rand2 env k)  (value-of rand2 env (kt_mul2_k v k))]
      [(mul2_k w k) (apply-k k (* w v))]
      [(sub_k k) (apply-k k (- v 1))]
      [(zero_k k) (apply-k k (zero? v))]
      [(throw_k vexp env) (value-of vexp env v)]
      [(proc_k rand env k) (value-of rand env (kt_arg_k v k))]
      [(arg_k p k) (apply-proc p v k)])))

(define-union envr
  (empty)
  (extend arg env))

(define apply-env
  (lambda (env num k)
    (union-case env envr
      [(empty) (error 'pc "unbound variable")]
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

(define main
  (lambda ()
    (value-of (exp_app
                        (exp_lambda
                          (exp_app
                            (exp_app (exp_var 0) (exp_var 0))
                            (exp_const 4)))
                        (exp_lambda
                          (exp_lambda
                            (exp_if (exp_zero (exp_var 0))
                                    (exp_const 1)
                                    (exp_mult (exp_var 0)
                                              (exp_app
                                                (exp_app (exp_var 1) (exp_var 1))
                                                (exp_sub1 (exp_var 0))))))))
                     (envr_empty) (kt_empty_k))))
    
