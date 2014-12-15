;;----------------------------------
;; B521 - Assignment 8
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

;============================================Part 1=================================================
; Common empty continuation constructors
(define empty-k
  (lambda ()
    `(empty-k)))
(define empty-k-exit
  (lambda (exit)
    `(empty-k ,exit)))

;----------------------------------------------------------------
; Transformations of the depth function
; ---------------------------------------------------------------
; Original CPSed depth
;;(define depth
;;  (lambda (ls k)
;;    (cond
;;      [(null? ls) (k 1)]
;;      [(pair? (car ls))
;;       (depth (car ls)
;;              (lambda (l)
;;                (depth (cdr ls)
;;                       (lambda (r)
;;                         (let ((l (add1 l)))
;;                           (k (if (< l r) r l)))))))]
;;      [else (depth (cdr ls) k)])))

; Continuation constructors
(define depth-inner-k
  (lambda (l k)
    `(depth-inner-k ,l ,k)))

(define depth-outer-k
  (lambda (ls k)
    `(depth-outer-k ,ls ,k)))

;-------------------------Registerization------------------------

; Registers for formal parameters of serious functions
(define *k*)
(define *ls*)
(define *v*)

; Registerized version of depth, i.e. depth-reg
(define depth-reg
  (lambda () ; remember we had ls and k
    (cond
      [(null? *ls*) (begin 
                      (set! *k* *k*) 
                      (set! *v* 1) 
                      (depth-apply-k-reg))]
      [(pair? (car *ls*)) (begin 
                            (set! *k* (depth-outer-k *ls* *k*)) 
                            (set! *ls* (car *ls*)) 
                            (depth-reg))]
      [else (begin
              (set! *k* *k*)
              (set! *ls* (cdr *ls*))
              (depth-reg))])))

; Registerized continuation observer
(define depth-apply-k-reg
  (lambda () ; remember we had k and v
    (pmatch *k*
      [(empty-k) *v*]
      [(depth-inner-k ,l ,k) (let ([l (add1 l)])
                               (begin
                                 (set! *k* k)
                                 (set! *v* (if (< l *v*) *v* l))
                                 (depth-apply-k-reg)))]
      [(depth-outer-k ,ls ,k) (begin
                                (set! *k* (depth-inner-k *v* k))
                                (set! *ls* (cdr ls))
                                (depth-reg))])))

; Driver for depth-reg, i.e. depth-reg-driver
(define depth-reg-driver
  (lambda (ls)
    (begin
      (set! *k* (empty-k))
      (set! *ls* ls)
      (depth-reg))))

;-------------------------Trampolining------------------------

; Note: I thought to try R.I. with thunks :)
; Trampolined version of depth, i.e. depth-tramp
(define depth-tramp
  (lambda (ls k)
    (depth-tramp-th ls k)))

; Trampolined continuation observer
(define depth-apply-k-tramp
  (lambda (k v)
    (depth-apply-k-tramp-th k v)))

; Depth thunk constructors
(define depth-tramp-th
  (lambda (ls k)
    `(depth-tramp-th ,ls ,k)))

(define depth-apply-k-tramp-th
  (lambda (k v)
    `(depth-apply-k-tramp-th ,k ,v)))

(define depth-init-th
  (lambda (ls exit)
    `(depth-init-th ,ls ,exit)))

; Depth thunk observer
(define depth-apply-th
  (lambda (th)
    (pmatch th
      [(depth-init-th ,ls ,exit) (depth-tramp ls (empty-k-exit exit))]
      [(depth-tramp-th ,ls ,k) (cond
                                 [(null? ls) (depth-apply-k-tramp k 1)]
                                 [(pair? (car ls)) (depth-tramp (car ls) (depth-outer-k ls k))]
                                 [else (depth-tramp (cdr ls) k)])]
      [(depth-apply-k-tramp-th ,k ,v) (pmatch k
                                        [(empty-k, exit) (exit v)]
                                        [(depth-inner-k ,l ,k) (let ([l (add1 l)])
                                                                 (depth-apply-k-tramp k (if (< l v) v l)))]
                                        [(depth-outer-k ,ls ,k) (depth-tramp (cdr ls) (depth-inner-k v k))])])))

; Trampoline to jump the lazy thunks (Note. now thunks are data structures)
(define depth-trampoline
  (lambda (th)
    (depth-trampoline (depth-apply-th th))))   

; Driver for depth-tramp, i.e. depth-tramp-driver
(define depth-tramp-driver
  (lambda (ls)
    (call/cc 
      (lambda (exit)
        (depth-trampoline (depth-init-th ls exit))))))

;-------------------------Test Cases------------------------
(define list-a '(1 9 (((3)9)) ((((((4))))))))
(define list-b '(1 9 ((((3))(9))) ((4)9) 0 (()())))
(define list-c '())

(printf "\n=================================================\nTests cases for Registerized Depth: depth-reg\n=================================================\n")
(test "depth-reg-a"
  (depth-reg-driver list-a)
  7)

(test "depth-reg-b"
  (depth-reg-driver list-b)
  5)

(test "depth-reg-c"
  (depth-reg-driver list-c)
  1)

(printf "\n=================================================\nTests cases for Trampolined Depth: depth-tramp\n=================================================\n")
(test "depth-tramp-a"
  (depth-tramp-driver list-a)
  7)

(test "depth-tramp-b"
  (depth-reg-driver list-b)
  5)

(test "depth-tramp-c"
  (depth-tramp-driver list-c)
  1)

;----------------------------------------------------------------
; Transformations of the ack function
; ---------------------------------------------------------------
;;(define ack
;;  (lambda (n m k)
;;    (cond
;;      [(zero? n) (k (add1 m))]
;;      [(zero? m) (ack (sub1 n) 1 k)]
;;      [else (ack n (sub1 m)
;;              (lambda (v)
;;	              (ack (sub1 n) v k)))])))

; Continuation constructors
(define ack-k
  (lambda (n k)
    `(ack-k ,n ,k)))

;-------------------------Trampolining------------------------

; Note: I did NOT use R.I. for thunks here :)
; Trampolined version of ack, i.e. ack-tramp
(define ack-tramp
  (lambda (n m k)
    (lambda() ; the nice thunk which puts everything to freeze
      (cond
        [(zero? n) (ack-apply-k-tramp k (add1 m))]
        [(zero? m) (ack-tramp (sub1 n) 1 k)]
        [else (ack-tramp n (sub1 m) (ack-k n k))]))))

; Continuation observer
(define ack-apply-k-tramp
  (lambda (k v)
    (lambda () ; the nice thunk which puts everything to freeze
      (pmatch k
        [(empty-k ,exit) (exit v)]
        [(ack-k ,n ,k) (ack-tramp (sub1 n) v k)]))))

; Trampoline to jump the lazy thunk
(define ack-trampoline
  (lambda (th)
    (ack-trampoline (th))))

; Driver for ack-tramp, i.e. ack-tramp-driver
(define ack-tramp-driver
  (lambda (n m)
    (call/cc
      (lambda (exit)
        (ack-trampoline (lambda () (ack-tramp n m (empty-k-exit exit))))))))

;-------------------------Registerization------------------------

; Registers for formal parameters of serious functions
(define *k* '*)
(define *n* '*)
(define *m* '*)
(define *v* '*)

; Registerized version of ack, i.e. ack-reg
(define ack-reg
  (lambda () ; remember we had n m and k
    (cond
      [(zero? *n*) (begin
                     (set! *k* *k*)
                     (set! *v* (add1 *m*))
                     (ack-apply-k-reg))]
      [(zero? *m*) (begin
                     (set! *k* *k*)
                     (set! *n* (sub1 *n*))
                     (set! *m* 1)
                     (ack-reg))]
      [else (begin
              (set! *k* (ack-k *n* *k*))
              (set! *n* *n*)
              (set! *m* (sub1 *m*))              
              (ack-reg))])))

; Continuation observer
(define ack-apply-k-reg
  (lambda () ; remember we had k and v
    (pmatch *k*
      [(empty-k) *v*]
      [(ack-k ,n ,k) (begin
                       (set! *k* k)
                       (set! *n* (sub1 n))
                       (set! *m* *v*)
                       (ack-reg))])))

; Driver for ack-reg, i.e. ack-reg-driver
(define ack-reg-driver
  (lambda (n m)
    (begin
      (set! *k* (empty-k))
      (set! *n* n)
      (set! *m* m)
      (ack-reg))))


;-------------------------Test Cases------------------------
(printf "\n=================================================\nTests cases for Trampolined Ack: ack-tramp\n=================================================\n")
(test "ack-tramp-a"
  (ack-tramp-driver 2 2)
  7)

(test "ack-tramp-b"
  (ack-tramp-driver 2 3)
  9)

(test "ack-tramp-c"
  (ack-tramp-driver 3 3)
  61)

;;(printf "\n=================================================\nTests cases for Registerized Ack: ack-reg\n=================================================\n")
(test "ack-reg-a"
  (ack-reg-driver 2 2)
  7)

(test "ack-reg-b"
  (ack-reg-driver 2 3)
  9)

(test "ack-reg-c"
  (ack-reg-driver 3 3)
  61)
;=========================================End of Part 1=============================================



;============================================Part 2=================================================
; Registerizing and Trampolining the Interpreter

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


;===============================Interpreter 1: value-of-cps============================
;--------------------------------------------------------------------------------------
; CPSed representation dependent (w.r.t. continuations) interpreter
; 
; Note: 1. Procedure helpers are based on data-structural representation
;       2. Environment helpers are based on data-structural representation
;--------------------------------------------------------------------------------------
(define value-of-cps
  (lambda (expr env k)
    (pmatch expr
      [,n (guard (or (number? n) (boolean? n))) (k n)]      
      [,x (guard (symbol? x)) (apply-env-cps env x k)]
      [(* ,x1 ,x2) (value-of-cps x1 env (lambda (v) (value-of-cps x2 env (lambda (w) (k (* v w))))))]
      [(sub1 ,x) (value-of-cps x env (lambda (v) (k (sub1 v))))]
      [(zero? ,x) (value-of-cps x env (lambda (v) (k (zero? v))))]
      [(if ,test ,conseq ,alt) (value-of-cps test env (lambda (v) (if v 
                                                                (value-of-cps conseq env k)
                                                                (value-of-cps alt env k))))]
;;    Original letcc line in the direct style interpreter
;;    [(letcc ,k-id ,body) (call/cc (lambda (k)
;;                                    (value-of body (extend-env k-id k env))))]
;;    The continuation we grab from call/cc is essentially the future waiting for
;;    the call/cc to finish. Now, in this cps version we get the particular future
;;    as k, so we don't want to invoke call/cc to grab it. Therefore, the line above
;;    becomes,
      [(letcc ,k-id ,body) (value-of-cps body (extend-env k-id k env) k)]
;;    originally, the second continuation would be something like (lambda (v) (c v))
;;    but this gave us the opportunity to do a eta transformation 
      [(throw ,v-exp ,k-exp) (value-of-cps k-exp env (lambda (c) (value-of-cps v-exp env c)))]
;;    (k (closure id body env)) is a tail call since closure is a simple thing which returns
;;    instantly, to be more clear think of this as (k `(clos ,id ,body, env))
      [(lambda (,id) ,body) (k (closure id body env))]
      [(,rator ,rand) (value-of-cps rand env (lambda (v) (value-of-cps rator env (lambda (w) (apply-proc-cps w v k)))))])))

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

;--------------------------------------------------------------------------------------
; Driver for value-of-cps, i.e. value-of-cps-driver
;--------------------------------------------------------------------------------------
(define value-of-cps-driver
  (lambda (expr)
    (value-of-cps expr (empty-env) (lambda (v) v))))

;--------------------------------------------------------------------------------------
; Test cases for Interpreter 1
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for Interpreter 1: value-of-cps\n=================================================\n")

(test "number"
  (value-of-cps-driver '10)
  10)

(test "boolean"
  (value-of-cps-driver '#f)
  #f)

(test "*"
  (value-of-cps-driver '(* 2 3))
  6)

(test "sub1"
  (value-of-cps-driver '(sub1 7))
  6)

(test "zero?-a"
  (value-of-cps-driver '(zero? 0))
  #t)

(test "zero?-b"
  (value-of-cps-driver '(zero? 1))
  #f)

(test "if-1"
  (value-of-cps-driver '(if #t #f #t))
  #f)

(test "if-2"
  (value-of-cps-driver '(if #f #f #t))
  #t)

(test "letcc-1"
  (value-of-cps-driver '(letcc k 5))
  5)

(test "letcc-2"
  (value-of-cps-driver '(* 2 (letcc k (throw 5 k))))
  10)

; shows that when throw is invoked the continuation at hand is forgotten, instead
; execution is transferred to the continuation given to the throw
(test "letcc-3"
  (value-of-cps-driver '(* 2 (letcc k (* 7 (throw 5 k)))))
  10)

(test "lambda-1"
  (value-of-cps-driver '((lambda (x) (* x x)) 4))
  16)

(test "lambda-2"
  (value-of-cps-driver '((lambda (x) (* 3 (letcc k (throw (* x x) k)))) 4))
  48)

(test "fact-5"
  (value-of-cps-driver fact-5)
  120)

(test "letcc"
  (value-of-cps-driver letcc-fun)
  12)

(test "letcc-fun-a"
  (value-of-cps-driver letcc-fun-a)
  6)

(test "letcc-fun-b"
  (value-of-cps-driver letcc-fun-b)
  30)

(test "letcc-fun-c"
  (value-of-cps-driver  letcc-fun-c)
  6)

(test "letcc-fun-d"
  (value-of-cps-driver  letcc-fun-d)
  4)

;===========================================End of Interpreter 1=================================================


;======================================Interpreter 2: value-of-cps-ri============================================
;--------------------------------------------------------------------------------------
; CPSed representation independent interpreter
; 
; Note: 1. Continuation helpers are based on data-strucutral representation
;       2. Procedure helpers are based on data-structural representation
;       3. Environment helpers are based on data-structural representation
;--------------------------------------------------------------------------------------
(define value-of-cps-ri
  (lambda (expr env k)
    (pmatch expr
      [,n (guard (or (number? n) (boolean? n))) (apply-k-ri k n)]      
      [,x (guard (symbol? x)) (apply-env-cps-ri env x k)]
      [(* ,x1 ,x2) (value-of-cps-ri x1 env (extend-v/k-*-1 x2 env k))]
      [(sub1 ,x) (value-of-cps-ri x env (extend-v/k-sub1 k))]
      [(zero? ,x) (value-of-cps-ri x env (extend-v/k-zero? k))]
      [(if ,test ,conseq ,alt) (value-of-cps-ri test env (extend-v/k-if conseq alt env k))]
      [(letcc ,k-id ,body) (value-of-cps-ri body (extend-env k-id k env) k)]
      [(throw ,v-exp ,k-exp) (value-of-cps-ri k-exp env (create-c v-exp env))]
      [(lambda (,id) ,body) (apply-k-ri k (closure id body env))]
      [(,rator ,rand) (value-of-cps-ri rand env (extend-a/k rator env k))])))

;--------------------------------------------------------------------------------------
; CPSed observers for envrionments and procedures based on data-structural 
; representation
;--------------------------------------------------------------------------------------
(define apply-env-cps-ri
 (lambda (env y k)
   (pmatch env
     [(mt-env) (error 'empty env "unbound variable ~s : discarding continuation" y)]
     [(ext-env ,x ,a ,env) (if (eq? x y) (apply-k-ri k a) (apply-env-cps-ri env y k))])))

(define apply-proc-cps-ri
  (lambda (p a k)
    (pmatch p
;;    Once again, the (extend-env ...) too returns instantly, thus, value-of-cps-ri
;;    call is a tail call
      [(clos ,id ,body ,env) (value-of-cps-ri body (extend-env id a env) k)])))

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
(define apply-k-ri
  (lambda (k v)
    (pmatch k
      [(empty-k) v]
      [(ext-a/k ,rator ,env, k) (value-of-cps-ri rator env (extend-p/k v k))]
      [(ext-p/k ,a ,k) (apply-proc-cps-ri v a k)]
      [(create-c ,exp ,env) (value-of-cps-ri exp env v)]
      [(ext-v/k-if ,conseq ,alt ,env ,k) (if v
                                              (value-of-cps-ri conseq env k)
                                              (value-of-cps-ri alt env k))]
      [(ext-v/k-zero? ,k) (apply-k-ri k (zero? v))]
      [(ext-v/k-sub1 ,k) (apply-k-ri k (sub1 v))]
      [(ext-v/k-*-1 ,x2 ,env ,k) (value-of-cps-ri x2 env (extend-v/k-*-2 v k))]
      [(ext-v/k-*-2 ,w ,k) (apply-k-ri k (* w v))])))

;--------------------------------------------------------------------------------------
; Driver for value-of-cps-ri, i.e. value-of-cps-ri-driver
;--------------------------------------------------------------------------------------
(define value-of-cps-ri-driver
  (lambda (expr)
    (value-of-cps-ri expr (empty-env) (empty-k))))

;--------------------------------------------------------------------------------------
; Test cases for Interpreter 2
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for Interpreter 2: value-of-cps-ri\n=================================================\n")

(test "number"
  (value-of-cps-ri-driver '10)
  10)

(test "boolean"
  (value-of-cps-ri-driver '#f)
  #f)

(test "*"
  (value-of-cps-ri-driver '(* 2 3))
  6)

(test "sub1"
  (value-of-cps-ri-driver '(sub1 7))
  6)

(test "zero?-a"
  (value-of-cps-ri-driver '(zero? 0))
  #t)

(test "zero?-b"
  (value-of-cps-ri-driver '(zero? 1))
  #f)

(test "if-1"
  (value-of-cps-ri-driver '(if #t #f #t))
  #f)

(test "if-2"
  (value-of-cps-ri-driver '(if #f #f #t))
  #t)

(test "letcc-1"
  (value-of-cps-ri-driver '(letcc k 5))
  5)

(test "letcc-2"
  (value-of-cps-ri-driver '(* 2 (letcc k (throw 5 k))))
  10)

; shows that when throw is invoked the continuation at hand is forgotten, instead
; execution is transferred to the continuation given to the throw
(test "letcc-3"
  (value-of-cps-ri-driver '(* 2 (letcc k (* 7 (throw 5 k)))))
  10)

(test "lambda-1"
  (value-of-cps-ri-driver '((lambda (x) (* x x)) 4))
  16)

(test "lambda-2"
  (value-of-cps-ri-driver '((lambda (x) (* 3 (letcc k (throw (* x x) k)))) 4))
  48)

(test "fact-5"
  (value-of-cps-ri-driver fact-5)
  120)

(test "letcc"
  (value-of-cps-ri-driver letcc-fun)
  12)

(test "letcc-fun-a"
  (value-of-cps-ri-driver letcc-fun-a)
  6)

(test "letcc-fun-b"
  (value-of-cps-ri-driver letcc-fun-b)
  30)

(test "letcc-fun-c"
  (value-of-cps-ri-driver letcc-fun-c)
  6)

(test "letcc-fun-d"
  (value-of-cps-ri-driver  letcc-fun-d)
  4)
;===========================================End of Interpreter 2=================================================


;======================================Interpreter 3: value-of-cps-ri-reg============================================
;--------------------------------------------------------------------------------------
; Registerized CPSed representation independent interpreter
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
; Registerized CPSed observers for envrionments and procedures based on data-structural 
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


;======================================Interpreter 4: value-of-cps-ri-reg-tramp============================================
;--------------------------------------------------------------------------------------
; Trampolined Registerized CPSed representation independent interpreter
; 
; Note: 1. Continuation helpers are based on data-strucutral representation
;       2. Procedure helpers are based on data-structural representation
;       3. Environment helpers are based on data-structural representation
;--------------------------------------------------------------------------------------

; Note: The registers are defined already above for Interpreter 3
(define value-of-cps-ri-reg-tramp
  (lambda () ; remember we had expr env and k. Also we can use this as the lazy thunk which puts everything to freeze
    (pmatch *expr*
      [,n (guard (or (number? n) (boolean? n))) (begin
                                                  (set! *k* *k*)
                                                  (set! *v* n)
                                                  apply-k-ri-reg-tramp)]      
      [,x (guard (symbol? x)) (begin
                                (set! *k* *k*)
                                (set! *env* *env*)
                                (set! *y* x)
                                apply-env-cps-ri-reg-tramp)]
      [(* ,x1 ,x2) (begin
                     (set! *k* (extend-v/k-*-1 x2 *env* *k*))
                     (set! *env* *env*)
                     (set! *expr* x1)
                     value-of-cps-ri-reg-tramp)]
      [(sub1 ,x) (begin
                   (set! *k* (extend-v/k-sub1 *k*))
                   (set! *env* *env*)
                   (set! *expr* x)
                   value-of-cps-ri-reg-tramp)]
      [(zero? ,x) (begin
                    (set! *k* (extend-v/k-zero? *k*))
                    (set! *env* *env*)
                    (set! *expr* x)
                    value-of-cps-ri-reg-tramp)]
      [(if ,test ,conseq ,alt) (begin
                                 (set! *k* (extend-v/k-if conseq alt *env* *k*))
                                 (set! *env* *env*)
                                 (set! *expr* test)
                                 value-of-cps-ri-reg-tramp)]
      [(letcc ,k-id ,body) (begin
                             (set! *k* *k*)
                             (set! *env* (extend-env k-id *k* *env*))
                             (set! *expr* body)
                             value-of-cps-ri-reg-tramp)]
      [(throw ,v-exp ,k-exp) (begin
                               (set! *k* (create-c v-exp *env*))
                               (set! *env* *env*)
                               (set! *expr* k-exp)
                               value-of-cps-ri-reg-tramp)]
      [(lambda (,id) ,body) (begin
                              (set! *k* *k*)
                              (set! *v* (closure id body *env*))
                              apply-k-ri-reg-tramp)]
      [(,rator ,rand) (begin
                        (set! *k* (extend-a/k rator *env* *k*))
                        (set! *env* *env*)
                        (set! *expr* rand)
                        value-of-cps-ri-reg-tramp)])))

;--------------------------------------------------------------------------------------
; CPSed observers for envrionments and procedures based on data-structural 
; representation
;--------------------------------------------------------------------------------------
(define apply-env-cps-ri-reg-tramp
 (lambda () ; remember we had env y and k. Also we can use this as the lazy thunk which puts everything to freeze
   (pmatch *env*
     [(mt-env) (error 'empty env "unbound variable ~s : discarding continuation" *y*)] ; hmm, I think we can improve this,
                                                                                       ; by creating a new error continuation and passing it. 
                                                                                       ; Not certain yet, though.
     [(ext-env ,x ,a ,env) (if (eq? x *y*) 
                             (begin
                               (set! *k* *k*)
                               (set! *v* a)
                               apply-k-ri-reg-tramp)
                             (begin
                               (set! *k* *k*)
                               (set! *env* env)
                               (set! *y* *y*)
                               apply-env-cps-ri-reg-tramp))])))
  

(define apply-proc-cps-ri-reg-tramp
  (lambda () ; remember we had p a and k. Also we can use this as the lazy thunk which puts everything to freeze
    (pmatch *p*
;;    Once again, the (extend-env ...) too returns instantly, thus, value-of-cps-ri-reg-tramp
;;    call is a tail call
      [(clos ,id ,body ,env) (begin
                               (set! *k* *k*)
                               (set! *env* (extend-env id *a* env))
                               (set! *expr* body)
                               value-of-cps-ri-reg-tramp)])))

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
(define apply-k-ri-reg-tramp
  (lambda () ; remember we had k and v. Also we can use this as the lazy thunk which puts everything to freeze
    (pmatch *k*
      [(empty-k, exit) (exit *v*)]
      [(ext-a/k ,rator ,env, k) (begin
                                  (set! *k* (extend-p/k *v* k))
                                  (set! *env* env)
                                  (set! *expr* rator)
                                  value-of-cps-ri-reg-tramp)]
      [(ext-p/k ,a ,k) (begin
                         (set! *k* k)
                         (set! *p* *v*)
                         (set! *a* a)
                         apply-proc-cps-ri-reg-tramp)]
      [(create-c ,exp ,env) (begin
                              (set! *k* *v*)
                              (set! *env* env)
                              (set! *expr* exp)
                              value-of-cps-ri-reg-tramp)]
      [(ext-v/k-if ,conseq ,alt ,env ,k) (if *v*
                                              (begin
                                                (set! *k* k)
                                                (set! *env* env)
                                                (set! *expr* conseq)
                                                value-of-cps-ri-reg-tramp)
                                              (begin
                                                (set! *k* k)
                                                (set! *env* env)
                                                (set! *expr* alt)
                                                value-of-cps-ri-reg-tramp))]
      [(ext-v/k-zero? ,k) (begin
                            (set! *k* k)
                            (set! *v* (zero? *v*))
                            apply-k-ri-reg-tramp)]
      [(ext-v/k-sub1 ,k) (begin
                           (set! *k* k)
                           (set! *v* (sub1 *v*))
                           apply-k-ri-reg-tramp)]
      [(ext-v/k-*-1 ,x2 ,env ,k) (begin
                                   (set! *k* (extend-v/k-*-2 *v* k))
                                   (set! *env* env)
                                   (set! *expr* x2)
                                   value-of-cps-ri-reg-tramp)]
      [(ext-v/k-*-2 ,w ,k) (begin
                             (set! *k* k)
                             (set! *v* (* w *v*))
                             apply-k-ri-reg-tramp)])))

;--------------------------------------------------------------------------------------
; Trampoline for value-of-cps-ri-reg-tramp, i.e. value-of-cps-ri-reg-tramp-trampoline
;--------------------------------------------------------------------------------------
(define value-of-cps-ri-reg-tramp-trampoline
  (lambda (th)
    (value-of-cps-ri-reg-tramp-trampoline (th))))

;--------------------------------------------------------------------------------------
; Driver for value-of-cps-ri-reg-tramp, i.e. value-of-cps-ri-reg-tramp-driver
;--------------------------------------------------------------------------------------
(define value-of-cps-ri-reg-tramp-driver
  (lambda (expr)
    (call/cc
      (lambda (exit)
        (value-of-cps-ri-reg-tramp-trampoline (lambda ()
                                                (begin
                                                  (set! *k* (empty-k-exit exit))
                                                  (set! *env* (empty-env))
                                                  (set! *expr* expr)
                                                  value-of-cps-ri-reg-tramp)))))))

;--------------------------------------------------------------------------------------
; Test cases for Interpreter 4
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for Interpreter 4: value-of-cps-ri-reg-tramp\n=================================================\n")

(test "number"
  (value-of-cps-ri-reg-tramp-driver '10)
  10)

(test "boolean"
  (value-of-cps-ri-reg-tramp-driver '#f)
  #f)

(test "*"
  (value-of-cps-ri-reg-tramp-driver '(* 2 3))
  6)

(test "sub1"
  (value-of-cps-ri-reg-tramp-driver '(sub1 7))
  6)

(test "zero?-a"
  (value-of-cps-ri-reg-tramp-driver '(zero? 0))
  #t)

(test "zero?-b"
  (value-of-cps-ri-reg-tramp-driver '(zero? 1))
  #f)

(test "if-1"
  (value-of-cps-ri-reg-tramp-driver '(if #t #f #t))
  #f)

(test "if-2"
  (value-of-cps-ri-reg-tramp-driver '(if #f #f #t))
  #t)

(test "letcc-1"
  (value-of-cps-ri-reg-tramp-driver '(letcc k 5))
  5)

(test "letcc-2"
  (value-of-cps-ri-reg-tramp-driver '(* 2 (letcc k (throw 5 k))))
  10)

; shows that when throw is invoked the continuation at hand is forgotten, instead
; execution is transferred to the continuation given to the throw
(test "letcc-3"
  (value-of-cps-ri-reg-tramp-driver '(* 2 (letcc k (* 7 (throw 5 k)))))
  10)

(test "lambda-1"
  (value-of-cps-ri-reg-tramp-driver '((lambda (x) (* x x)) 4))
  16)

(test "lambda-2"
  (value-of-cps-ri-reg-tramp-driver '((lambda (x) (* 3 (letcc k (throw (* x x) k)))) 4))
  48)

(test "fact-5"
  (value-of-cps-ri-reg-tramp-driver fact-5)
  120)

(test "letcc"
  (value-of-cps-ri-reg-tramp-driver letcc-fun)
  12)

(test "letcc-fun-a"
  (value-of-cps-ri-reg-tramp-driver letcc-fun-a)
  6)

(test "letcc-fun-b"
  (value-of-cps-ri-reg-tramp-driver letcc-fun-b)
  30)

(test "letcc-fun-c"
  (value-of-cps-ri-reg-tramp-driver letcc-fun-c)
  6)

(test "letcc-fun-d"
  (value-of-cps-ri-reg-tramp-driver  letcc-fun-d)
  4)
;===========================================End of Interpreter 4=================================================

;================================================End of Part 2===================================================



;====================================================Part 3======================================================
;--------------------------------------------------------------------------------------
; Hard Brainteaser
;--------------------------------------------------------------------------------------

; Note: I am not sure what is the (fact 5), (fact -1), etc. calls are, because if the 
;       definition of fact is the trampolined version of original factorial then it should
;       take more than one argument, i.e. number and continuation. 
;
;       Thus, I assume that the definition of fact would be a driver which sets an empty
;       continuation. The empty continuation would grab an exit continuation from a register
;       and throw the value to it.

; Register to hold the exit continuation
(define *exit* '*)

(define fact-exit-k
  (lambda ()
    `(exit-k)))

(define fact-k
  (lambda (k n)
    `(fact-k ,k ,n)))

(define fact-tramp
  (lambda (n k)
    (lambda ()
      (if (= n 0)
        (fact-apply-k k 1)
        (fact-tramp (sub1 n) (fact-k k n))))))

(define fact-apply-k
  (lambda (k v)
    (pmatch k
      [(exit-k) (*exit* v)] ; grab the exit continuation from the register and throw v into that
      [(fact-k ,k ,n) (fact-apply-k k (* n v))])))

; Note. This is what I thought fact to be
(define fact
  (lambda (n)
    (lambda () (fact-tramp n (fact-exit-k)))))

; The important part :) a two thunk trampoline to jump one lazy thunk after the other
(define trampoline
  (lambda (th1 th2)
    (trampoline (th2) th1))) ; Note. the swapping of thunks

(define first
  (lambda (thnk1 thnk2)
    (call/cc
      (lambda (exit)
        (begin
          (set! *exit* exit) ; sets the exit continuation
          (trampoline thnk1 thnk2))))))

(printf "\n=================================================\nTests cases for Hard Brainteaser: first\n=================================================\n")

(test "first-a"
  (first (lambda () (fact 5)) (lambda () (fact 20)))
  120)

(test "first-b"
  (first (lambda () (fact -1)) (lambda () (fact 20)))
  2432902008176640000)

(test "first-c"
  (first (lambda () (fact 20)) (lambda () (fact -1)))
  2432902008176640000)

(test "first-d"
  (first (lambda () (fact 0)) (lambda () (fact 2)))
  1)