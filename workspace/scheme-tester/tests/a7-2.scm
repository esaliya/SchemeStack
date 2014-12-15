;;----------------------------------
;; B521 - Assignment 7
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    0002560797
;; Email: sekanaya@indiana.edu
;;----------------------------------
 
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

;--------------------------------------------------------------------------------------
; CPSed representation independent interpreter
; 
; Note: 1. Continuation helpers are based on procedural representation
;       2. Procedure helpers are based on data-structural representation
;       3. Environment helpers are based on data-structural representation
;--------------------------------------------------------------------------------------
(define value-of-cps-fn
  (lambda (expr env k)
    (pmatch expr
      [,n (guard (or (number? n) (boolean? n))) (apply-k k n)]      
      [,x (guard (symbol? x)) (apply-env-cps env x k)]
      [(* ,x1 ,x2) (value-of-cps-fn x1 env (extend-v/k-*-1 x2 env k))]
      [(sub1 ,x) (value-of-cps-fn x env (extend-v/k-sub1 k))]
      [(zero? ,x) (value-of-cps-fn x env (extend-v/k-zero? k))]
      [(if ,test ,conseq ,alt) (value-of-cps-fn test env (extend-v/k-if conseq alt env k))]
;;    Original letcc line in the direct style interpreter
;;    [(letcc ,k-id ,body) (call/cc (lambda (k)
;;                                    (value-of body (extend-env k-id k env))))]
;;    The continuation we grab from call/cc is essentially the future waiting for
;;    the call/cc to finish. Now, in this cps version we get the particular future
;;    as k, so we don't want to invoke call/cc to grab it. Therefore, the line above
;;    becomes,
      [(letcc ,k-id ,body) (value-of-cps-fn body (extend-env k-id k env) k)]
;;    originally, the second continuation would be something like (lambda (v) (c v))
;;    but this gave us the opportunity to do a eta transformation 
      [(throw ,v-exp ,k-exp) (value-of-cps-fn k-exp env (create-c v-exp env))]
;;    (k (closure id body env)) is a tail call since closure is a simple thing which returns
;;    instantly, to be more clear think of this as (k `(clos ,id ,body, env))
      [(lambda (,id) ,body) (apply-k k (closure id body env))]
      [(,rator ,rand) (value-of-cps-fn rand env (extend-a/k rator env k))])))



;--------------------------------------------------------------------------------------
; Continuation helpers based on procedural representation 
;--------------------------------------------------------------------------------------
(define init-k-fn
  (lambda ()
    (lambda (x) x)))q

(define apply-k
  (lambda (k v)
    (k v)))

; "you expect an argument, so extend the continuation to do what is necessary with the argument"
(define extend-a/k
  (lambda (rator env k)
    ; 'a is the expected argument
    (lambda (a) (value-of-cps-fn rator env (extend-p/k a k)))))

; "you expect a procedure, so extend the continuation to do what is necessary with the procedure"
(define extend-p/k
  (lambda (a k)
    ; 'p is the expected procedure
    (lambda (p) (apply-proc-cps p a k))))
  

; "you expect a continuation, so create a new continuation to do what is necessary with the expected continuation
(define create-c
  (lambda (exp env)
    ; 'c is the expected continuation
    (lambda (c) (value-of-cps-fn exp env c))))

; "you expect a value, so extend the continuation to do what is necessary with the value for 'if"
(define extend-v/k-if
  (lambda (conseq alt env k)
    (lambda (v) (if v
                  (value-of-cps-fn conseq env k)
                  (value-of-cps-fn alt env k)))))

; "you expect a value, so extend the continuation to do what is necessary with the value for 'zero?"
(define extend-v/k-zero?
  (lambda (k)
    (lambda (v) (k (zero? v)))))

; "you expect a value, so extend the continuation to do what is necessary with the value for 'sub1"
(define extend-v/k-sub1
  (lambda (k)
    (lambda (v) (k (sub1 v)))))

; "you expect the first value to *, so extend the continuation to do what is necessary with the value
; to complete '*"
(define extend-v/k-*-1
  (lambda (x2 env k)
    ; 'v is the expected first value for *
    (lambda (v) (value-of-cps-fn x2 env (extend-v/k-*-2 v k)))))

; "you expect the second value to * and you have the first value to *, so extend the continuation to 
; do what is necessary with the value to complete '*"
(define extend-v/k-*-2
  ; 'v is the first value to '*
  (lambda (v k)
    ; 'w is the expected second value to '*
    (lambda (w) (k (* v w)))))



;--------------------------------------------------------------------------------------
; Environment and procedure helpers based on data structure representation 
;--------------------------------------------------------------------------------------
(define empty-env
  (lambda ()
    `(mt-env)))

(define extend-env
 (lambda (x a env)
   `(ext-env ,x ,a ,env)))

(define apply-env-cps
 (lambda (env y k)
   (pmatch env
     [(mt-env) (error 'empty env "unbound variable ~s : discarding continuation" y)]
     [(ext-env ,x ,a ,env) (if (eq? x y) (k a) (apply-env-cps env y k))])))

(define closure
  (lambda (id body env)
    `(clos ,id ,body ,env)))

(define apply-proc-cps
  (lambda (p a k)
    (pmatch p
;;    Once again, the (extend-env ...) too returns instantly, thus, value-of-cps-fn
;;    call is a tail call
      [(clos ,id ,body ,env) (value-of-cps-fn body (extend-env id a env) k)])))