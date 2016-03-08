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

(define-union envr
  (empty)
  (extend arg env))

(define-union clos
  (closure code env))

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

(define value-of
  (lambda () ;expr env k
    (union-case *expr* exp
      [(const n) (begin
;;                   (set! *k* *k*)
                   (set! *v* n)
                   (apply-k))]
      [(var v) (begin
;;                 (set! *env* *env*)
                 (set! *num* v)
;;                 (set! *k* *k*)
                 (apply-env))]
      [(if test conseq alt) (begin
                              (set! *k* (kont_if-k conseq alt *env* *k*))
                              (set! *expr* test)
;;                              (set! *env* *env*)
                              (value-of))]
      [(mult rand1 rand2) (begin
                            (set! *k* (kont_mult-k1 rand2 *env* *k*))
                            (set! *expr* rand1)
;;                            (set! *env* *env*)
                            (value-of))]
      [(sub1 rand) (begin
                     (set! *k* (kont_sub1-k *k*))
                     (set! *expr* rand)
;;                     (set! *env* *env*)
                     (value-of))]
      [(zero rand) (begin
                     (set! *k* (kont_zero?-k *k*))
                     (set! *expr* rand)
;;                     (set! *env* *env*)
                     (value-of))]
      [(letcc body) (begin
                      (set! *env* (envr_extend *k* *env*))
                      (set! *expr* body)
                      (value-of))]
      [(throw vexp kexp) (begin
                           (set! *k* (kont_c-k vexp *env*))
                           (set! *expr* kexp)
;;                           (set! *env* *env*)
                           (value-of))]
      [(let vexp body) (begin
                         (set! *k* (kont_let-k body *env* *k*))
                         (set! *expr* vexp)
                         (set! *env* *env*)
                         (value-of))]
      [(lambda body) (begin
;;                       (set! *k* *k*)
                       (set! *v* (clos_closure body *env*))
                       (apply-k))]
      [(app rator rand) (begin
                          (set! *k* (kont_proc-k rand *env* *k*))
                          (set! *expr* rator)
;;                          (set! *env* *env*)
                          (value-of))])))

(define apply-env
  (lambda () ;env num k
    (union-case *env* envr
      [(empty) (errorf 'env "unbound variable")]
      [(extend arg env)
       (if (zero? *num*)
           (begin
;;             (set! *k* *k*)
             (set! *v* arg)
             (apply-k))
           (begin
;;             (set! *k* *k*)
             (set! *num* (sub1 *num*))
             (set! *env* env)
             (apply-env)))])))



(define apply-proc
  (lambda () ;c a k
    (union-case *c* clos
      [(closure code env) (begin
;;                            (set! *k* *k*)
                            (set! *expr* code)
                            (set! *env* (envr_extend *a* env))
                            (value-of))])))

(define apply-k
  (lambda () ;k v
    (union-case *k* kont
      [(empty-k) *v*]
      [(mult-k1 rand2 env k) (begin
                               (set! *k* (kont_mult-k2 *v* k))
                               (set! *expr* rand2)
                               (set! *env* env)
                               (value-of))]
      [(mult-k2 w k) (begin
                       (set! *k* k)
                       (set! *v* (* w *v*))
                       (apply-k))]
      [(sub1-k k) (begin
                    (set! *k* k)
                    (set! *v* (sub1 *v*))
                    (apply-k))]
      [(zero?-k k) (begin
                     (set! *k* k)
                     (set! *v* (zero? *v*))
                     (apply-k))]
      [(if-k conseq alt env k) (if *v* (begin
                                         (set! *k* k)
                                         (set! *expr* conseq)
                                         (set! *env* env)
                                         (value-of))
                                   (begin
                                     (set! *k* k)
                                     (set! *expr* alt)
                                     (set! *env* env)
                                     (value-of)))]
      [(c-k vexp env) (begin
                        (set! *k* *v*)
                        (set! *expr* vexp)
                        (set! *env* env)
                        (value-of))]
      [(let-k body env k) (begin
                            (set! *k* k)
                            (set! *expr* body)
                            (set! *env* (envr_extend *v* env))
                            (value-of))]
      [(proc-k rand env k) (begin
                             (set! *k* (kont_arg-k *v* k))
                             (set! *expr* rand)
                             (set! *env* env)
                             (value-of))]
      [(arg-k proc k) (begin
                        (set! *k* k)
                        (set! *c* proc)
                        (set! *a* *v*)
                        (apply-proc))])))

;----------------------tests-----------------------------------

(pretty-print
  (begin
    (set! *expr* (exp_app
                  (exp_app (exp_lambda (exp_var 0)) (exp_lambda (exp_var 0)))
                  (exp_const 5)))
    (set! *env* (envr_empty))
    (set! *k* (kont_empty-k))
    (value-of)))

; Factorial of 5...should be 120.
;;((lambda (f)
;;   ((f f) 5))
;; (lambda (f)
;;   (lambda (n)
;;     (if (zero? n)
;;         1
;;         (* n ((f f) (sub1 n)))))))
;; 
(pretty-print
  (begin
    (set! *expr* (exp_app
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
                                       (exp_sub1 (exp_var 0)))))))))
    (set! *env* (envr_empty))
    (set! *k* (kont_empty-k))
    (value-of)))

                                        ; Test of letcc and throw...should evaluate to 24.
;;      (pretty-print
;;        (begin
;;          (set! *expr* (exp_mult (exp_const 2)
;;                                 (exp_letcc
;;                                  (exp_mult (exp_const 5)
;;                                            (exp_throw (exp_mult (exp_const 2) (exp_const 6))
;;                                                       (exp_var 0))))))
;;          (set! *env* (envr_empty))
;;          (set! *k* (kont_empty-k))
;;          (value-of)))

;; (let ([fact (lambda (f)                                                      
;;               (lambda (n)                                                    
;;                 (if (zero? n)                                                
;;                     1                                                        
;;                     (* n ((f f) (sub1 n))))))])                              
;;   ((fact fact) 5))                                                           

;;      (pretty-print
;;        (begin
;;          (set! *expr* (exp_let
;;                        (exp_lambda
;;                         (exp_lambda
;;                          (exp_if
;;                           (exp_zero (exp_var 0))
;;                           (exp_const 1)
;;                           (exp_mult
;;                            (exp_var 0)
;;                            (exp_app
;;                             (exp_app (exp_var 1) (exp_var 1))
;;                             (exp_sub1 (exp_var 0)))))))
;;                        (exp_app (exp_app (exp_var 0) (exp_var 0)) (exp_const 5))))
;;          (set! *env* (envr_empty))
;;          (set! *k* (kont_empty-k))
;;          (value-of)))
