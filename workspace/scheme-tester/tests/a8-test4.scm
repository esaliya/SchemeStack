;----------------------------------------------------------------
; Test macro (taken happily from the assignment itself :))
; ---------------------------------------------------------------
(define-syntax test
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (let* ((expected expected-result)
            (produced tested-expression))
       (if (equal? expected produced)
           (printf "~s works!\n" title)
           (error
            'test
            "Failed ~s: ~a\nExpected: ~a\nComputed: ~a"
            title 'tested-expression expected produced))))))

;----------------------------------------------------------------
; Global test definitions
; ---------------------------------------------------------------
(define fact-5
  '((lambda (f)
      ((f f) 5))
    (lambda (f)
      (lambda (n)
        (if (zero? n)
            1
            (* n ((f f) (sub1 n))))))))
 
(define letcc-fun
  '(* 3 (letcc q (* 2 (throw 4 q)))))

(define letcc-fun-a
  '(* 2 (letcc k (* (letcc c (throw 3 k)) 5))))

; the inner throw will discard the outer throw. Thus, 3 is multiplied by 5 as the result
; of inner throw. This is the value of the first letcc body. so it's (15) returned as the
; value of first letcc call. So it will eventually get multiplied by 2 resulting 30.
(define letcc-fun-b
  '(* 2 (letcc k (* (letcc c (throw (throw 3 c) k)) 5))))

; here the continuation represented by g is thrown another continuation k. In fact, g
; represented a continuation which was waiting for some continuation (i.e. the throw 3 
; call and the reset following it). The net effect is that 3 is thrown to k which is the
; continuation of multiply by 2. So the result is 6
(define letcc-fun-c
  '(* 2 (letcc k (* (letcc c (throw (throw 3 (letcc g (throw k g))) k)) 5))))

(define letcc-fun-d
  '((lambda (x) (letcc k (throw x k))) 4)) 

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

; Common empty continuation constructors
(define empty-k
  (lambda ()
    `(empty-k)))
(define empty-k-exit
  (lambda (exit)
    `(empty-k ,exit)))

;****************************************************************************************************************

;======================================Interpreter 3: value-of-cps-ri-reg============================================
;--------------------------------------------------------------------------------------
; CPSed representation independent interpreter
; 
; Note: 1. Continuation helpers are based on data-strucutral representation
;       2. Procedure helpers are based on data-structural representation
;       3. Environment helpers are based on data-structural representation
;--------------------------------------------------------------------------------------
(define *expr* '*)
(define *env* '*)
(define *k* '*)
(define *env* '*)
(define *y* '*)
(define *p* '*)
(define *a* '*)
(define *v* '*)

(define value-of-cps-ri-reg
  (lambda () ; remember we had expr env and k
    (pmatch *expr*
      [,n (guard (or (number? n) (boolean? n))) (begin
                                                  (set! *k* *k*)
                                                  (set! *v* n)
                                                  (apply-k-ri-reg))]      
      [,x (guard (symbol? x)) (begin
                                (set! *k* *k*)
                                (set! *env* *env*)
                                (set! *y* x)
                                (apply-env-cps-ri-reg))]
      [(* ,x1 ,x2) (begin
                     (set! *k* (extend-v/k-*-1 x2 *env* *k*))
                     (set! *env* *env*)
                     (set! *expr* x1)
                     (value-of-cps-ri-reg))]
      [(sub1 ,x) (begin
                   (set! *k* (extend-v/k-sub1 *k*))
                   (set! *env* *env*)
                   (set! *expr* x)
                   (value-of-cps-ri-reg))]
      [(zero? ,x) (begin
                    (set! *k* (extend-v/k-zero? *k*))
                    (set! *env* *env*)
                    (set! *expr* x)
                    (value-of-cps-ri-reg))]
      [(if ,test ,conseq ,alt) (begin
                                 (set! *k* (extend-v/k-if conseq alt *env* *k*))
                                 (set! *env* *env*)
                                 (set! *expr* test)
                                 (value-of-cps-ri-reg))]
      [(letcc ,k-id ,body) (begin
                             (set! *k* *k*)
                             (set! *env* (extend-env k-id *k* *env*))
                             (set! *expr* body)
                             (value-of-cps-ri-reg))]
      [(throw ,v-exp ,k-exp) (begin
                               (set! *k* (create-c v-exp *env*))
                               (set! *env* *env*)
                               (set! *expr* k-exp)
                               (value-of-cps-ri-reg))]
      [(lambda (,id) ,body) (begin
                              (set! *k* *k*)
                              (set! *v* (closure id body *env*))
                              (apply-k-ri-reg))]
      [(,rator ,rand) (begin
                        (set! *k* (extend-a/k rator *env* *k*))
                        (set! *env* *env*)
                        (set! *expr* rand)
                        (value-of-cps-ri-reg))])))

;--------------------------------------------------------------------------------------
; CPSed observers for envrionments and procedures based on data-structural 
; representation
;--------------------------------------------------------------------------------------
(define apply-env-cps-ri-reg
 (lambda () ; remember we had env y and k
   (pmatch *env*
     [(mt-env) (error 'empty env "unbound variable ~s : discarding continuation" *y*)]
     [(ext-env ,x ,a ,env) (if (eq? x *y*) 
                             (begin
                               (set! *k* *k*)
                               (set! *v* a)
                               (apply-k-ri-reg))
                             (begin
                               (set! *k* *k*)
                               (set! *env* env)
                               (set! *y* *y*)
                               (apply-env-cps-ri-reg)))])))
  

(define apply-proc-cps-ri-reg
  (lambda () ; remember we had p a and k
    (pmatch *p*
;;    Once again, the (extend-env ...) too returns instantly, thus, value-of-cps-ri-reg
;;    call is a tail call
      [(clos ,id ,body ,env) (begin
                               (set! *k* *k*)
                               (set! *env* (extend-env id *a* env))
                               (set! *expr* body)
                               (value-of-cps-ri-reg))])))

;--------------------------------------------------------------------------------------
; Constructors for continuations based on data-structural representation
;--------------------------------------------------------------------------------------
(define extend-a/k
  (lambda (rator env k)
    `(ext-a/k ,rator ,env, k)))

(define extend-p/k
  (lambda (a k)    
    `(ext-p/k ,a ,k)))
  
(define create-c
  (lambda (exp env)    
    `(create-c ,exp ,env)))

(define extend-v/k-if
  (lambda (conseq alt env k)
    `(ext-v/k-if ,conseq ,alt ,env ,k)))

(define extend-v/k-zero?
  (lambda (k)
    `(ext-v/k-zero? ,k)))

(define extend-v/k-sub1
  (lambda (k)
    `(ext-v/k-sub1 ,k)))

(define extend-v/k-*-1
  (lambda (x2 env k)    
    `(ext-v/k-*-1 ,x2 ,env ,k)))

(define extend-v/k-*-2  
  (lambda (v k)   
    `(ext-v/k-*-2 ,v ,k)))

;--------------------------------------------------------------------------------------
; Observers for continuations based on data-structural representation
;--------------------------------------------------------------------------------------
(define apply-k-ri-reg
  (lambda () ; remember we had k and v
    (pmatch *k*
      [(empty-k) *v*]
      [(ext-a/k ,rator ,env, k) (begin
                                  (set! *k* (extend-p/k *v* k))
                                  (set! *env* env)
                                  (set! *expr* rator)
                                  (value-of-cps-ri-reg))]
      [(ext-p/k ,a ,k) (begin
                         (set! *k* k)
                         (set! *p* *v*)
                         (set! *a* a)
                         (apply-proc-cps-ri-reg))]
      [(create-c ,exp ,env) (begin
                              (set! *k* *v*)
                              (set! *env* env)
                              (set! *expr* exp)
                              (value-of-cps-ri-reg))]
      [(ext-v/k-if ,conseq ,alt ,env ,k) (if *v*
                                              (begin
                                                (set! *k* k)
                                                (set! *env* env)
                                                (set! *expr* conseq)
                                                (value-of-cps-ri-reg))
                                              (begin
                                                (set! *k* k)
                                                (set! *env* env)
                                                (set! *expr* alt)
                                                (value-of-cps-ri-reg)))]
      [(ext-v/k-zero? ,k) (begin
                            (set! *k* k)
                            (set! *v* (zero? *v*))
                            (apply-k-ri-reg))]
      [(ext-v/k-sub1 ,k) (begin
                           (set! *k* k)
                           (set! *v* (sub1 *v*))
                           (apply-k-ri-reg))]
      [(ext-v/k-*-1 ,x2 ,env ,k) (begin
                                   (set! *k* (extend-v/k-*-2 *v* k))
                                   (set! *env* env)
                                   (set! *expr* x2)
                                   (value-of-cps-ri-reg))]
      [(ext-v/k-*-2 ,w ,k) (begin
                             (set! *k* k)
                             (set! *v* (* w *v*))
                             (apply-k-ri-reg))])))

;--------------------------------------------------------------------------------------
; Driver for value-of-cps-ri-reg, i.e. value-of-cps-ri-reg-driver
;--------------------------------------------------------------------------------------
(define value-of-cps-ri-reg-driver
  (lambda (expr)
    (begin
      (set! *k* (empty-k))
      (set! *env* (empty-env))
      (set! *expr* expr)
      (value-of-cps-ri-reg))))

;--------------------------------------------------------------------------------------
; Test cases for Interpreter 3
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for Interpreter 3: value-of-cps-ri-reg\n=================================================\n")

(test "number"
  (value-of-cps-ri-reg-driver '10)
  10)

(test "boolean"
  (value-of-cps-ri-reg-driver '#f)
  #f)

(test "*"
  (value-of-cps-ri-reg-driver '(* 2 3))
  6)

(test "sub1"
  (value-of-cps-ri-reg-driver '(sub1 7))
  6)

(test "zero?-a"
  (value-of-cps-ri-reg-driver '(zero? 0))
  #t)

(test "zero?-b"
  (value-of-cps-ri-reg-driver '(zero? 1))
  #f)

(test "if-1"
  (value-of-cps-ri-reg-driver '(if #t #f #t))
  #f)

(test "if-2"
  (value-of-cps-ri-reg-driver '(if #f #f #t))
  #t)

(test "letcc-1"
  (value-of-cps-ri-reg-driver '(letcc k 5))
  5)

(test "letcc-2"
  (value-of-cps-ri-reg-driver '(* 2 (letcc k (throw 5 k))))
  10)

; shows that when throw is invoked the continuation at hand is forgotten, instead
; execution is transferred to the continuation given to the throw
(test "letcc-3"
  (value-of-cps-ri-reg-driver '(* 2 (letcc k (* 7 (throw 5 k)))))
  10)

(test "lambda-1"
  (value-of-cps-ri-reg-driver '((lambda (x) (* x x)) 4))
  16)

(test "lambda-2"
  (value-of-cps-ri-reg-driver '((lambda (x) (* 3 (letcc k (throw (* x x) k)))) 4))
  48)

(test "fact-5"
  (value-of-cps-ri-reg-driver fact-5)
  120)

(test "letcc"
  (value-of-cps-ri-reg-driver letcc-fun)
  12)

(test "letcc-fun-a"
  (value-of-cps-ri-reg-driver letcc-fun-a)
  6)

(test "letcc-fun-b"
  (value-of-cps-ri-reg-driver letcc-fun-b)
  30)

(test "letcc-fun-c"
  (value-of-cps-ri-reg-driver letcc-fun-c)
  6)

(test "letcc-fun-d"
  (value-of-cps-ri-reg-driver  letcc-fun-d)
  4)
;===========================================End of Interpreter 3=================================================