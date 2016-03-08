;;----------------------------------
;; B521 - Assignment 9
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    0002560797
;; Email: sekanaya@indiana.edu
;;----------------------------------

;----------------------------------------------------------------
; Registerized R.I., w.r.t. continuations, CPSed interpreter
; ---------------------------------------------------------------
; register definitions
(define-registers expr env k v num c a)
(define-program-counter pc)

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
  (lambda () ; remember we had expr env and k
    (union-case expr exp
      [(const n) (begin                   
                   (set! v n)
                   (set! pc apply-k))]
      [(var v) (begin
                 (set! num v)
                 (set! pc apply-env))]
      [(if test conseq alt) (begin
                              (set! k (kt_if_k conseq alt env k))
                              (set! expr test)                              
                              (set! pc value-of))]
      [(mult rand1 rand2) (begin
                            (set! k (kt_mul1_k rand2 env k))
                            (set! expr rand1)
                            (set! pc value-of))]
      [(sub1 rand) (begin
                     (set! k (kt_sub_k k))
                     (set! expr rand)
                     (set! pc value-of))]
      [(zero rand) (begin
                     (set! k (kt_zero_k k))
                     (set! expr rand)
                     (set! pc value-of))]
      [(letcc body) (begin
                      (set! expr body)
                      (set! env (envr_extend k env))
                      (set! pc value-of))]
      [(throw vexp kexp) (begin
                           (set! k (kt_throw_k vexp env))
                           (set! expr kexp)
                           (set! pc value-of))]
      [(lambda body) (begin                       
                       (set! v (clos_closure body env))
                       (set! pc apply-k))]
      [(app rator rand) (begin
                          (set! k (kt_proc_k rand env k))
                          (set! expr rator)
                          (set! pc value-of))])))

(define-union kt
  (empty_k dismount)
  (if_k conseq alt env k)
  (mul1_k rand2 env k)
  (mul2_k w k)
  (sub_k k)
  (zero_k k)
  (throw_k vexp env)
  (proc_k rand env k)
  (arg_k p k))
   
(define apply-k
  (lambda () ; remember we had k and v
    (union-case k kt
      [(empty_k dismount) (dismount-trampoline dismount)]
      [(if_k conseq alt env^ k^) (if v
                                    (begin
                                      (set! k k^)
                                      (set! expr conseq)
                                      (set! env env^)
                                      (set! pc value-of))
                                    (begin
                                      (set! k k^)
                                      (set! expr alt)
                                      (set! env env^)
                                      (set! pc value-of)))]      
      [(mul1_k rand2 env^ k^)  (begin
                                  (set! k (kt_mul2_k v k^))
                                  (set! expr rand2)
                                  (set! env env^)
                                  (set! pc value-of))]
      [(mul2_k w k^) (begin
                        (set! k k^)
                        (set! v (* w v))
                        (set! pc apply-k))]
      [(sub_k k^) (begin
                     (set! k k^)
                     (set! v (- v 1))
                     (set! pc apply-k))]
      [(zero_k k^) (begin
                      (set! k k^)
                      (set! v (zero? v))
                      (set! pc apply-k))]
      [(throw_k vexp env^) (begin
                             (set! k v)
                             (set! expr vexp)
                             (set! env env^)
                             (set! pc value-of))]
      [(proc_k rand env^ k^) (begin
                                (set! k (kt_arg_k v k^))
                                (set! expr rand)
                                (set! env env^)
                                (set! pc value-of))]
      [(arg_k p k^) (begin
                       (set! c p)
                       (set! a v)
                       (set! k k^)
                       (set! pc apply-proc))])))

(define-union envr
  (empty)
  (extend arg env))

(define apply-env
  (lambda () ; remember we had env num and k
    (union-case env envr
      [(empty) (error 'pc "unbound variable")]
      [(extend arg env^) (if (zero? num)
                           (begin                             
                             (set! v arg)
                             (set! pc apply-k))
                           (begin
                             (set! env env^)
                             (set! num (sub1 num))
                             (set! pc apply-env)))])))

(define-union clos
  (closure code env))

(define apply-proc
  (lambda () ; remember we had c a and k
    (union-case c clos
      [(closure code env^) (begin
                             (set! expr code)
                             (set! env (envr_extend a env^))
                             (set! pc value-of))])))    

(define main
  (lambda ()
    (begin
      (set! expr (exp_app
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
      (set! env (envr_empty))
      (set! pc value-of)
      (mount-trampoline kt_empty_k k pc)
      (printf "factorial 5: ~d\n" v))))