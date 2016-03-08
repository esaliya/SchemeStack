                                        ; Added pc and trampolinized

(define-registers *expr* *env* *k* *v* *num* *c* *a*)
(define-program-counter *pc*)

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

(define-label value-of
  (union-case *expr* exp
    [(const n) (begin
                 (set! *v* n)
                 (set! *pc* apply-k))]
    [(var v) (begin
               (set! *num* v)
               (set! *pc* apply-env))]
    [(if test conseq alt) (begin
                            (set! *k* (kont_if-k conseq alt *env* *k*))
                            (set! *expr* test)
                            (set! *pc* value-of))]
    [(mult rand1 rand2) (begin
                          (set! *k* (kont_mult-k1 rand2 *env* *k*))
                          (set! *expr* rand1)
                          (set! *pc* value-of))]
    [(sub1 rand) (begin
                   (set! *k* (kont_sub1-k *k*))
                   (set! *expr* rand)
                   (set! *pc* value-of))]
    [(zero rand) (begin
                   (set! *k* (kont_zero?-k *k*))
                   (set! *expr* rand)
                   (set! *pc* value-of))]
    [(letcc body) (begin
                    (set! *env* (envr_extend *k* *env*))
                    (set! *expr* body)
                    (set! *pc* value-of))]
    [(throw vexp kexp) (begin
                         (set! *k* (kont_c-k vexp *env*))
                         (set! *expr* kexp)
                         (set! *pc* value-of))]
    [(let vexp body) (begin
                       (set! *k* (kont_let-k body *env* *k*))
                       (set! *expr* vexp)
                       (set! *pc* value-of))]
    [(lambda body) (begin
                     (set! *v* (clos_closure body *env*))
                     (set! *pc* apply-k))]
    [(app rator rand) (begin
                        (set! *k* (kont_proc-k rand *env* *k*))
                        (set! *expr* rator)
                        (set! *pc* value-of))]))

(define-union envr
  (empty)
  (extend arg env))

(define-label apply-env
  (union-case *env* envr
    [(empty) (errorf 'env "unbound variable")]
    [(extend arg env)
     (if (zero? *num*)
         (begin
           (set! *v* arg)
           (set! *pc* apply-k))
         (begin
           (set! *num* (sub1 *num*))
           (set! *env* env)
           (set! *pc* apply-env)))]))

(define-union clos
  (closure code env))

(define-label apply-proc
  (union-case *c* clos
    [(closure code env) (begin
                          (set! *expr* code)
                          (set! *env* (envr_extend *a* env))
                          (set! *pc* value-of))]))

(define-union kont
  (empty-k dismount)
  (mult-k1 rand2 env k)
  (mult-k2 w k)
  (sub1-k k)
  (zero?-k k)
  (if-k conseq alt env k)
  (c-k vexp env)
  (let-k body env k)
  (proc-k rand env k)
  (arg-k proc k))



(define-label apply-k
  (union-case *k* kont
    [(empty-k dismount) (dismount-trampoline dismount)]
    [(mult-k1 rand2 env k) (begin
                             (set! *k* (kont_mult-k2 *v* k))
                             (set! *expr* rand2)
                             (set! *env* env)
                             (set! *pc* value-of))]
    [(mult-k2 w k) (begin
                     (set! *k* k)
                     (set! *v* (* w *v*))
                     (set! *pc* apply-k))]
    [(sub1-k k) (begin
                  (set! *k* k)
                  (set! *v* (sub1 *v*))
                  (set! *pc* apply-k))]
    [(zero?-k k) (begin
                   (set! *k* k)
                   (set! *v* (zero? *v*))
                   (set! *pc* apply-k))]
    [(if-k conseq alt env k) (if *v* (begin
                                       (set! *k* k)
                                       (set! *expr* conseq)
                                       (set! *env* env)
                                       (set! *pc* value-of))
                                 (begin
                                   (set! *k* k)
                                   (set! *expr* alt)
                                   (set! *env* env)
                                   (set! *pc* value-of)))]
    [(c-k vexp env) (begin
                      (set! *k* *v*)
                      (set! *expr* vexp)
                      (set! *env* env)
                      (set! *pc* value-of))]
    [(let-k body env k) (begin
                          (set! *k* k)
                          (set! *expr* body)
                          (set! *env* (envr_extend *v* env))
                          (set! *pc* value-of))]
    [(proc-k rand env k) (begin
                           (set! *k* (kont_arg-k *v* k))
                           (set! *expr* rand)
                           (set! *env* env)
                           (set! *pc* value-of))]
    [(arg-k proc k) (begin
                      (set! *k* k)
                      (set! *c* proc)
                      (set! *a* *v*)
                      (set! *pc* apply-proc))]))



;-----------------main function-----------------------------
(define-label main
  (begin
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
      (set! *pc* value-of)
      (mount-trampoline kont_empty-k *k* *pc*)
      (printf "~s\n" *v*))
    (begin
      (set! *expr* (exp_mult (exp_const 2)
                             (exp_letcc
                              (exp_mult (exp_const 5)
                                        (exp_throw (exp_mult (exp_const 2) (exp_const 6))
                                                   (exp_var 0))))))
      (set! *env* (envr_empty))
      (set! *pc* value-of)
      (mount-trampoline kont_empty-k *k* *pc*)
      (printf "~s\n" *v*))

    (begin
      (set! *expr* (exp_let
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
                    (exp_app (exp_app (exp_var 0) (exp_var 0)) (exp_const 5))))
      (set! *env* (envr_empty))
      (set! *pc* value-of)
      (mount-trampoline kont_empty-k *k* *pc*)
      (printf "~s\n" *v*))))


