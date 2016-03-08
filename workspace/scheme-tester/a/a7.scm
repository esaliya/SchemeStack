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

 
;======================================Interpreter 1: value-of-cps===============================================
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
; Test cases for Interpreter 1
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for Interpreter 1: value-of-cps\n=================================================\n")

(test "number"
  (value-of-cps '10 (empty-env) (lambda (x) x))
  10)

(test "boolean"
  (value-of-cps '#f (empty-env) (lambda (x) x))
  #f)

(test "*"
  (value-of-cps '(* 2 3) (empty-env) (lambda (x) x))
  6)

(test "sub1"
  (value-of-cps '(sub1 7) (empty-env) (lambda (x) x))
  6)

(test "zero?-a"
  (value-of-cps '(zero? 0) (empty-env) (lambda (x) x))
  #t)

(test "zero?-b"
  (value-of-cps '(zero? 1) (empty-env) (lambda (x) x))
  #f)

(test "if-1"
  (value-of-cps '(if #t #f #t) (empty-env) (lambda (x) x))
  #f)

(test "if-2"
  (value-of-cps '(if #f #f #t) (empty-env) (lambda (x) x))
  #t)

(test "letcc-1"
  (value-of-cps '(letcc k 5) (empty-env) (lambda (x) x))
  5)

(test "letcc-2"
  (value-of-cps '(* 2 (letcc k (throw 5 k))) (empty-env) (lambda (x) x))
  10)

; shows that when throw is invoked the continuation at hand is forgotten, instead
; execution is transferred to the continuation given to the throw
(test "letcc-3"
  (value-of-cps '(* 2 (letcc k (* 7 (throw 5 k)))) (empty-env) (lambda (x) x))
  10)

(test "lambda-1"
  (value-of-cps '((lambda (x) (* x x)) 4) (empty-env) (lambda (x) x))
  16)

(test "lambda-2"
  (value-of-cps '((lambda (x) (* 3 (letcc k (throw (* x x) k)))) 4) (empty-env) (lambda (x) x))
  48)

(test "fact-5"
  (value-of-cps fact-5 (empty-env) (lambda (x) x))
  120)

(test "letcc"
  (value-of-cps letcc-fun (empty-env) (lambda (x) x))
  12)

(test "letcc-fun-a"
  (value-of-cps letcc-fun-a (empty-env) (lambda (x) x))
  6)

(test "letcc-fun-b"
  (value-of-cps letcc-fun-b (empty-env) (lambda (x) x))
  30)

(test "letcc-fun-c"
  (value-of-cps  letcc-fun-c (empty-env) (lambda (x) x))
  6)

(test "letcc-fun-d"
  (value-of-cps  letcc-fun-d (empty-env) (lambda (x) x))
  4)

;===========================================End of Interpreter 1=================================================



;======================================Interpreter 2: value-of-cps-fn============================================
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
      [,x (guard (symbol? x)) (apply-env-cps-fn env x k)]
      [(* ,x1 ,x2) (value-of-cps-fn x1 env (extend-v/k-*-1 x2 env k))]
      [(sub1 ,x) (value-of-cps-fn x env (extend-v/k-sub1 k))]
      [(zero? ,x) (value-of-cps-fn x env (extend-v/k-zero? k))]
      [(if ,test ,conseq ,alt) (value-of-cps-fn test env (extend-v/k-if conseq alt env k))]
      [(letcc ,k-id ,body) (value-of-cps-fn body (extend-env k-id k env) k)]
      [(throw ,v-exp ,k-exp) (value-of-cps-fn k-exp env (create-c v-exp env))]
      [(lambda (,id) ,body) (apply-k k (closure id body env))]
      [(,rator ,rand) (value-of-cps-fn rand env (extend-a/k rator env k))])))

;--------------------------------------------------------------------------------------
; CPSed observers for environments and procedures based on data-structural 
; representation
;--------------------------------------------------------------------------------------
(define apply-env-cps-fn
 (lambda (env y k)
   (pmatch env
     [(mt-env) (error 'empty env "unbound variable ~s : discarding continuation" y)]
     [(ext-env ,x ,a ,env) (if (eq? x y) (apply-k k a) (apply-env-cps-fn env y k))])))

(define apply-proc-cps-fn
  (lambda (p a k)
    (pmatch p
;;    Once again, the (extend-env ...) too returns instantly, thus, value-of-cps-fn
;;    call is a tail call
      [(clos ,id ,body ,env) (value-of-cps-fn body (extend-env id a env) k)])))

;--------------------------------------------------------------------------------------
; Constructors for continuations based on procedural representation
;--------------------------------------------------------------------------------------
; initial continuation
(define empty-k-fn
  (lambda ()
    (lambda (x) x)))

; "you expect an argument, so extend the continuation to do what is necessary with the argument"
(define extend-a/k
  (lambda (rator env k)
    ; 'a is the expected argument
    (lambda (a) (value-of-cps-fn rator env (extend-p/k a k)))))

; "you expect a procedure, so extend the continuation to do what is necessary with the procedure"
(define extend-p/k
  (lambda (a k)
    ; 'p is the expected procedure
    (lambda (p) (apply-proc-cps-fn p a k))))
  

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
    (lambda (v) (apply-k k (zero? v)))))

; "you expect a value, so extend the continuation to do what is necessary with the value for 'sub1"
(define extend-v/k-sub1
  (lambda (k)
    (lambda (v) (apply-k k (sub1 v)))))

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
    (lambda (w) (apply-k k (* v w)))))

;--------------------------------------------------------------------------------------
; Observers for continuations based on procedural representation
;--------------------------------------------------------------------------------------
(define apply-k
  (lambda (k v)
    (k v)))

;--------------------------------------------------------------------------------------
; Test cases for Interpreter 2
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for Interpreter 2: value-of-cps-fn\n=================================================\n")

(test "number"
  (value-of-cps-fn '10 (empty-env) (empty-k-fn))
  10)

(test "boolean"
  (value-of-cps-fn '#f (empty-env) (empty-k-fn))
  #f)

(test "*"
  (value-of-cps-fn '(* 2 3) (empty-env) (empty-k-fn))
  6)

(test "sub1"
  (value-of-cps-fn '(sub1 7) (empty-env) (empty-k-fn))
  6)

(test "zero?-a"
  (value-of-cps-fn '(zero? 0) (empty-env) (empty-k-fn))
  #t)

(test "zero?-b"
  (value-of-cps-fn '(zero? 1) (empty-env) (empty-k-fn))
  #f)

(test "if-1"
  (value-of-cps-fn '(if #t #f #t) (empty-env) (empty-k-fn))
  #f)

(test "if-2"
  (value-of-cps-fn '(if #f #f #t) (empty-env) (empty-k-fn))
  #t)

(test "letcc-1"
  (value-of-cps-fn '(letcc k 5) (empty-env) (empty-k-fn))
  5)

(test "letcc-2"
  (value-of-cps-fn '(* 2 (letcc k (throw 5 k))) (empty-env) (empty-k-fn))
  10)

; shows that when throw is invoked the continuation at hand is forgotten, instead
; execution is transferred to the continuation given to the throw
(test "letcc-3"
  (value-of-cps-fn '(* 2 (letcc k (* 7 (throw 5 k)))) (empty-env) (empty-k-fn))
  10)

(test "lambda-1"
  (value-of-cps-fn '((lambda (x) (* x x)) 4) (empty-env) (empty-k-fn))
  16)

(test "lambda-2"
  (value-of-cps-fn '((lambda (x) (* 3 (letcc k (throw (* x x) k)))) 4) (empty-env) (empty-k-fn))
  48)

(test "fact-5"
  (value-of-cps-fn fact-5 (empty-env) (empty-k-fn))
  120)

(test "letcc"
  (value-of-cps-fn letcc-fun (empty-env) (empty-k-fn))
  12)

(test "letcc-fun-a"
  (value-of-cps-fn letcc-fun-a (empty-env) (empty-k-fn))
  6)

(test "letcc-fun-b"
  (value-of-cps-fn letcc-fun-b (empty-env) (empty-k-fn))
  30)

(test "letcc-fun-c"
  (value-of-cps-fn letcc-fun-c (empty-env) (empty-k-fn))
  6)

(test "letcc-fun-d"
  (value-of-cps-fn  letcc-fun-d (empty-env) (empty-k-fn))
  4)
;===========================================End of Interpreter 2=================================================



;======================================Interpreter 3: value-of-cps-ds============================================
;--------------------------------------------------------------------------------------
; CPSed representation independent interpreter
; 
; Note: 1. Continuation helpers are based on data-strucutral representation
;       2. Procedure helpers are based on data-structural representation
;       3. Environment helpers are based on data-structural representation
;--------------------------------------------------------------------------------------
(define value-of-cps-ds
  (lambda (expr env k)
    (pmatch expr
      [,n (guard (or (number? n) (boolean? n))) (apply-k-ds k n)]      
      [,x (guard (symbol? x)) (apply-env-cps-ds env x k)]
      [(* ,x1 ,x2) (value-of-cps-ds x1 env (extend-v/k-*-1-ds x2 env k))]
      [(sub1 ,x) (value-of-cps-ds x env (extend-v/k-sub1-ds k))]
      [(zero? ,x) (value-of-cps-ds x env (extend-v/k-zero?-ds k))]
      [(if ,test ,conseq ,alt) (value-of-cps-ds test env (extend-v/k-if-ds conseq alt env k))]
      [(letcc ,k-id ,body) (value-of-cps-ds body (extend-env k-id k env) k)]
      [(throw ,v-exp ,k-exp) (value-of-cps-ds k-exp env (create-c-ds v-exp env))]
      [(lambda (,id) ,body) (apply-k-ds k (closure id body env))]
      [(,rator ,rand) (value-of-cps-ds rand env (extend-a/k-ds rator env k))])))

;--------------------------------------------------------------------------------------
; CPSed observers for envrionments and procedures based on data-structural 
; representation
;--------------------------------------------------------------------------------------
(define apply-env-cps-ds
 (lambda (env y k)
   (pmatch env
     [(mt-env) (error 'empty env "unbound variable ~s : discarding continuation" y)]
     [(ext-env ,x ,a ,env) (if (eq? x y) (apply-k-ds k a) (apply-env-cps-ds env y k))])))

(define apply-proc-cps-ds
  (lambda (p a k)
    (pmatch p
;;    Once again, the (extend-env ...) too returns instantly, thus, value-of-cps-ds
;;    call is a tail call
      [(clos ,id ,body ,env) (value-of-cps-ds body (extend-env id a env) k)])))

;--------------------------------------------------------------------------------------
; Constructors for continuations based on data-structural representation
;--------------------------------------------------------------------------------------
; initial continuation
(define empty-k-ds
  (lambda ()
    `(initial-cont)))

(define extend-a/k-ds
  (lambda (rator env k)
    `(ext-a/k-ds ,rator ,env, k)))

(define extend-p/k-ds
  (lambda (a k)    
    `(ext-p/k-ds ,a ,k)))
  
(define create-c-ds
  (lambda (exp env)    
    `(create-c-ds ,exp ,env)))

(define extend-v/k-if-ds
  (lambda (conseq alt env k)
    `(ext-v/k-if-ds ,conseq ,alt ,env ,k)))

(define extend-v/k-zero?-ds
  (lambda (k)
    `(ext-v/k-zero?-ds ,k)))

(define extend-v/k-sub1-ds
  (lambda (k)
    `(ext-v/k-sub1-ds ,k)))

(define extend-v/k-*-1-ds
  (lambda (x2 env k)    
    `(ext-v/k-*-1-ds ,x2 ,env ,k)))

(define extend-v/k-*-2-ds  
  (lambda (v k)   
    `(ext-v/k-*-2-ds ,v ,k)))

;--------------------------------------------------------------------------------------
; Observers for continuations based on data-structural representation
;--------------------------------------------------------------------------------------
(define apply-k-ds
  (lambda (k v)
    (pmatch k
      [(initial-cont) v]
      [(ext-a/k-ds ,rator ,env, k) (value-of-cps-ds rator env (extend-p/k-ds v k))]
      [(ext-p/k-ds ,a ,k) (apply-proc-cps-ds v a k)]
      [(create-c-ds ,exp ,env) (value-of-cps-ds exp env v)]
      [(ext-v/k-if-ds ,conseq ,alt ,env ,k) (if v
                                              (value-of-cps-ds conseq env k)
                                              (value-of-cps-ds alt env k))]
      [(ext-v/k-zero?-ds ,k) (apply-k-ds k (zero? v))]
      [(ext-v/k-sub1-ds ,k) (apply-k-ds k (sub1 v))]
      [(ext-v/k-*-1-ds ,x2 ,env ,k) (value-of-cps-ds x2 env (extend-v/k-*-2-ds v k))]
      [(ext-v/k-*-2-ds ,w ,k) (apply-k-ds k (* w v))])))

;--------------------------------------------------------------------------------------
; Test cases for Interpreter 3
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for Interpreter 3: value-of-cps-ds\n=================================================\n")

(test "number"
  (value-of-cps-ds '10 (empty-env) (empty-k-ds))
  10)

(test "boolean"
  (value-of-cps-ds '#f (empty-env) (empty-k-ds))
  #f)

(test "*"
  (value-of-cps-ds '(* 2 3) (empty-env) (empty-k-ds))
  6)

(test "sub1"
  (value-of-cps-ds '(sub1 7) (empty-env) (empty-k-ds))
  6)

(test "zero?-a"
  (value-of-cps-ds '(zero? 0) (empty-env) (empty-k-ds))
  #t)

(test "zero?-b"
  (value-of-cps-ds '(zero? 1) (empty-env) (empty-k-ds))
  #f)

(test "if-1"
  (value-of-cps-ds '(if #t #f #t) (empty-env) (empty-k-ds))
  #f)

(test "if-2"
  (value-of-cps-ds '(if #f #f #t) (empty-env) (empty-k-ds))
  #t)

(test "letcc-1"
  (value-of-cps-ds '(letcc k 5) (empty-env) (empty-k-ds))
  5)

(test "letcc-2"
  (value-of-cps-ds '(* 2 (letcc k (throw 5 k))) (empty-env) (empty-k-ds))
  10)

; shows that when throw is invoked the continuation at hand is forgotten, instead
; execution is transferred to the continuation given to the throw
(test "letcc-3"
  (value-of-cps-ds '(* 2 (letcc k (* 7 (throw 5 k)))) (empty-env) (empty-k-ds))
  10)

(test "lambda-1"
  (value-of-cps-ds '((lambda (x) (* x x)) 4) (empty-env) (empty-k-ds))
  16)

(test "lambda-2"
  (value-of-cps-ds '((lambda (x) (* 3 (letcc k (throw (* x x) k)))) 4) (empty-env) (empty-k-ds))
  48)

(test "fact-5"
  (value-of-cps-ds fact-5 (empty-env) (empty-k-ds))
  120)

(test "letcc"
  (value-of-cps-ds letcc-fun (empty-env) (empty-k-ds))
  12)

(test "letcc-fun-a"
  (value-of-cps-ds letcc-fun-a (empty-env) (empty-k-ds))
  6)

(test "letcc-fun-b"
  (value-of-cps-ds letcc-fun-b (empty-env) (empty-k-ds))
  30)

(test "letcc-fun-c"
  (value-of-cps-ds letcc-fun-c (empty-env) (empty-k-ds))
  6)

(test "letcc-fun-d"
  (value-of-cps-ds  letcc-fun-d (empty-env) (empty-k-ds))
  4)
;===========================================End of Interpreter 3=================================================



;================================================Brainteasers====================================================
;--------------------------------------------------------------------------------------
; Background info   
;--------------------------------------------------------------------------------------
; The laws to be satisfied
;; (grow base) = (lambda (m) m)   Note: The change of c to m with alpha substitution
;; ((o (grow f)) base) = f
;--------------------------------------------------------------------------------------
; The defintion of function o
;;(define o
;;  (lambda (f)
;;    (lambda (g)
;;      (lambda (x)
;;        (f (g x))))))
;--------------------------------------------------------------------------------------


;======================================================================================
; Brainteaser 1: Devise a definition for base w.r.t. the following grow function
;--------------------------------------------------------------------------------------

;;(define grow
;;  (lambda (f)
;;    (lambda (c)
;;      (lambda (s)
;;        (pmatch (c s)
;;          ((,a . ,s^) ((f a) s^)))))))

;--------------------------------------------------------------------------------------
; Derivation of base to satisfy first law, i.e. (grow base) = (lambda (m) m)
;--------------------------------------------------------------------------------------
; Beta substitute base into grow

;;(lambda (c)
;;  (lambda (s)
;;    (pmatch (c s)
;;      [(,a . ,s^) ((base a) s^)])))

; Note: 1. c is a single argument function
;       2. base should be a curried function of the form,

;;(define base
;;  (lambda (a)
;;    (lambda (s^)
;;      ...)))

; If the result of the beta substitution is to be equal to (lambda (m) m) then,

;;(lambda (s)
;;  (pmatch (c s)
;;    [(,a . ,s^) ((base a) s^)]))

; should be equal to c. This along with note 1, implies that,

;;(pmatch (c s)
;;    [(,a . ,s^) ((base a) s^)])

; should be equal to (c s). This implies that,

;;((base a) s^)

; should produce `(,a . ,s^). So from note 2 we can define base (say def-A) as

;;(define base
;;  (lambda (a)
;;    (lambda (s^)
;;      `(,a . ,s^))))

;--------------------------------------------------------------------------------------
; Derivation of base to satisfy second law, i.e. (((o (grow f)) base) = f
;--------------------------------------------------------------------------------------
; Goal: the derrivation of base for this case should produce the same defintion
;       as def-A

; Beta substitute (grow f) into o and base into (o (grow f)), i.e. ((o (grow f)) base) 
; is equal to,

;;(lambda (x)
;;  ((grow f) (base x)))

; Now, beta substitute f into grow to get,

;;(lambda (x)
;;  ((lambda (c)
;;     (lambda (s)
;;       (pmatch (c s)
;;         [(,a . ,s^) ((f a) s^)])))
;;   (base x)))

; Now, beta substitute (base x) to get,

;;(lambda (x)
;;  (lambda (s)
;;    (pmatch ((base x) s)
;;      [(,a . ,s^) ((f a) s^)])))

; Note: 1. base is curried of the form,

;;(lambda (x)
;;  (lambda (s)
;;    ...))

;       2. f is curried similarly, so if some other function is to be equal to f then 
;          that function should be of the form,

;;(lambda (a)
;;  (lambda (s^)
;;    ((f a) s^)))

; Now we see that the result of the last beta substitution would be of the form note 2 if
; ((base x) s) produced `(,x . ,s). So we can now define base (say def-B) as,

;;(define base
;;  (lambda (x)
;;    (lambda (s)
;;      `(,x . ,s))))

;--------------------------------------------------------------------------------------
; Conclusion 
;--------------------------------------------------------------------------------------
; A simple alpha substitution shows that def-A and def-B are equal. Therefore, we have
; derrived the correct definition for base which is,

;;(define base
;;  (lambda (x)
;;    (lambda (s)
;;      `(,x . ,s))))
;======================================================================================



;======================================================================================
; Brainteaser 2: Devise a definition for base w.r.t. the following grow function
;--------------------------------------------------------------------------------------

;;(define grow
;;  (lambda (f)
;;    (lambda (c)
;;      (lambda (k)
;;        (c (lambda (a)
;;             ((f a) k)))))))

;--------------------------------------------------------------------------------------
; Derivation of base to satisfy first law, i.e. (grow base) = (lambda (m) m)
;--------------------------------------------------------------------------------------
; Beta substitute base into grow

;;(lambda (c)
;;  (lambda (k)
;;    (c (lambda (a)
;;         ((base a) k)))))

; Note: 1. c is a single argument function
;       2. base should be a curried function of the form,

;;(define base
;;  (lambda (a)
;;    (lambda (k)
;;      ...)))

; If the result of the beta substitution is to be equal to (lambda (m) m) then,

;;(lambda (k)
;;  (c (lambda (a)
;;       ((base a) k))))

; should be equal to c. This along with note 1, implies that,

;;(c (lambda (a)
;;     ((base a) k)))

; should be equal to (c k). This implies that,

;;(lambda (a)
;;  ((base a) k))

; should be equal to k. This implies that,

;;((base a) k)

; should produce (k a). So from note 2 we can define base (say def-C) as

;;(define base
;;  (lambda (a)
;;    (lambda (k)
;;      (k a))))

;--------------------------------------------------------------------------------------
; Derivation of base to satisfy second law, i.e. (((o (grow f)) base) = f
;--------------------------------------------------------------------------------------
; Goal: the derrivation of base for this case should produce the same defintion
;       as def-C

; Beta substitute (grow f) into o and base into (o (grow f)), i.e. ((o (grow f)) base) 
; is equal to,

;;(lambda (x)
;;  ((grow f) (base x)))

; Now, beta substitute f into grow to get,

;;(lambda (x)
;;  ((lambda (c)
;;     (lambda (k)
;;       (c (lambda (a)
;;            ((f a) k)))))
;;   (base x)))

; Now, beta substitute (base x) to get,

;;(lambda (x)
;;  (lambda (k)
;;    ((base x) (lambda (a)
;;                ((f a) k)))))

; Note: 1. base is curried of the form,

;;(lambda (x)
;;  (lambda (f)
;;    ...))

;       2. f is curried similarly, so if some other function is to be equal to f then 
;          that function should be of the form,

;;(lambda (a)
;;  (lambda (k)
;;    ((f a) k)))

; Now we see that the result of the last beta substitution would be of the form note 2 if
; (base x) returned a procedure which, accepts another procedure of one argument and then 
; apply that procedure to x. Thus, we can define base (say def-D) as,

;;(define base
;;  (lambda (x)
;;    (lambda (f)
;;      (f s))))

;--------------------------------------------------------------------------------------
; Conclusion 
;--------------------------------------------------------------------------------------
; A simple alpha substitution shows that def-C and def-D are equal. Therefore, we have
; derrived the correct definition for base which is,

;;(define base
;;  (lambda (x)
;;    (lambda (f)
;;      (f s))))
;======================================================================================



;======================================================================================
; Brainteaser 3: Devise a definition for base w.r.t. the following grow function
;--------------------------------------------------------------------------------------

;;(define grow
;;  (lambda (f)
;;    (lambda (c)
;;      (pmatch c
;;        [(inR . ,e) c]
;;        [(inL . ,a) (f a)]))))

;--------------------------------------------------------------------------------------
; Derivation of base to satisfy first law, i.e. (grow base) = (lambda (m) m)
;--------------------------------------------------------------------------------------
; Beta substitute base into grow

;;(lambda (c)
;;  (pmatch c
;;    [(inR . ,e) c]
;;    [(inL . ,a) (base a)]))

; Note: 1. first pmatch case returns back c

; If the result of the beta substitution is to be equal to (lambda (m) m) then,

;;(pmatch c
;;  [(inR . ,e) c]
;;  [(inL . ,a) (base a)])

; should be equal to c. This along with note 1, implies that,

;;(base a)

; should produce c which, for this case is `(inL . ,a). So we can define base (say def-E) as

;;(define base
;;  (lambda (a)
;;    `(inL . ,a)))

;--------------------------------------------------------------------------------------
; Derivation of base to satisfy second law, i.e. (((o (grow f)) base) = f
;--------------------------------------------------------------------------------------
; Goal: the derrivation of base for this case should produce the same defintion
;       as def-E

; Beta substitute (grow f) into o and base into (o (grow f)), i.e. ((o (grow f)) base) 
; is equal to,

;;(lambda (x)
;;  ((grow f) (base x)))

; Now, beta substitute f into grow to get,

;;(lambda (x)
;;  ((lambda (c)
;;     (pmatch c
;;       [(inR . ,e) c]
;;       [(inL . ,a) (f a)]))
;;   (base x)))

; Now, beta substitute (base x) to get,

;;(lambda (x)
;;  (pmatch (base x)
;;    [(inR . ,e) (base x)]
;;    [(inL . ,a) (f a)]))

; Note: 1. f is a single argument function

; If the result of the last beta substitution is to be equal to f then,

;;(pmatch (base x)
;;  [(inR . ,e) (base x)]
;;  [(inL . ,a) (f a)])

; should equal to (f a). This is possible if (base x) produced `(inL . ,x)
; which would satisfy second pmatch condition and would result in (f x). Thus,
; we can define base (say def-F) as,

;;(define base
;;  (lambda (x)
;;    `(inL . ,x)))

;--------------------------------------------------------------------------------------
; Conclusion 
;--------------------------------------------------------------------------------------
; A simple alpha substitution shows that def-E and def-F are equal. Therefore, we have
; derrived the correct definition for base which is,

;;(define base
;;  (lambda (x)
;;    `(inL . ,x)))
;======================================================================================

