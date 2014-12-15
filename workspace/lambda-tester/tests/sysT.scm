;; ----------------------------------------------------------------------------
;; System T Interpreter in Scheme 
;; ----------------------------------------------------------------------------
;; 
;; System T
;; --------     
;;   Expressions e ::= x | zero | succ e | lambda x:T.e | e e
;;                     | natrec e {zero => e | succ x with y => e}
;; 
;;   Types       T ::= nat | T -> T
;; 
;; Modified Syntax
;; ----------------
;;               e :: = x | zero | (succ e) | (lambda x e) | (e e)
;;                      | (natrec e (zero e) (succ x with y e))
;;
;;   Type checking is not done in the implementation
;; 
;; Evaluation Strategy
;; --------------------
;;   Call-by-name
;; ----------------------------------------------------------------------------
(define value-of
  (lambda (e env)
    (match e
      [zero 'zero]
      [(succ ,e) `(succ ,(value-of e env))]
      [(lambda ,x ,e) (closure x e env)]
      [(natrec ,e (zero ,e0) (succ ,x with ,y ,e1))
       (let ([ev (value-of e env)])
         (match ev
           [zero (value-of e0 env)]
           [(succ ,ev^) 
            (value-of 
             e1 
             (extend-env 
              (extend-env env x (value-wrap ev^))
              y 
              (value-wrap
               (value-of
                `(natrec ,ev^ (zero ,e0) (succ x with y ,e1))
                env))))]))]
      [(,rator ,rand) (guard (and (symbol? rand) (not (eq? 'zero rand))))
       (apply-proc (value-of rator env) (apply-env env rand))]
      [(,rator ,rand)
       (apply-proc (value-of rator env) (arg-wrap rand env))]
      [,x (guard (symbol? x)) (unwrap (apply-env env x))]
      [,x (error 'value-of (format "invalid input: ~s" x))])))

(define closure
  (lambda (x e env)
    `(closure ,x ,e ,env)))

(define apply-proc
  (lambda (p a)
    (match p
      [(closure ,x ,e ,env) (value-of e (extend-env env x a))]
      [,x (error 'apply-prof (format "invalid closure: ~s" x))])))

(define empty-env
  (lambda ()
    `(empty-env)))

(define extend-env
  (lambda (env x v)
    `(extend-env ,x ,v ,env)))

(define apply-env
  (lambda (env x)
    (match env
      [(extend-env ,x^ ,v ,env)
       (if (eq? x x^) v (apply-env env x))]
      [(empty-env) (error 'apply-env "env is empty!")]))) 
                    
(define arg-wrap
  (lambda (rand env)
    `(arg-wrap ,rand ,env)))

(define value-wrap
  (lambda (v)
    `(value-wrap ,v)))

(define unwrap
  (lambda (w)
    (match w
      [(arg-wrap ,rand ,env) (value-of rand env)]
      [(value-wrap ,v) v]
      [,x (error 'unwrap (format "invalid wrap: ~s" x))])))
;; ----------------------------------------------------------------------------


;; ----------------------------------------------------------------------------
;; Test macro (taken happily from B521 :))
;; ----------------------------------------------------------------------------
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
;; ----------------------------------------------------------------------------


;; ----------------------------------------------------------------------------
;; Test cases
;; ----------------------------------------------------------------------------
(define plus
  '(lambda a (lambda b (natrec a (zero b) (succ _ with y (succ y))))))

(define mult
  `(lambda a (lambda b (natrec a (zero zero) (succ _ with y ,(encode-plus 'b 'y))))))

(define fact
  `(lambda a (natrec a (zero (succ zero)) (succ x with y ,(encode-mult '(succ x) 'y)))))

(define exp
  `(lambda a (lambda b (natrec b (zero (succ zero)) (succ _ with y ,(encode-mult 'a 'y))))))

(define pred
  `(lambda a (natrec a (zero zero) (succ x with _ x))))

(define sub
  `(lambda a (lambda b (natrec b (zero a) (succ _ with y ,(encode-pred 'y))))))

(define encode-plus 
  (lambda (a b)
    `((,plus ,a) ,b)))

(define encode-mult
  (lambda (a b)
    `((,mult ,a) ,b)))

(define encode-fact
  (lambda (a)
    `(,fact ,a)))

(define encode-exp
  (lambda (a b)
    `((,exp ,a) ,b)))

(define encode-pred
  (lambda (a)
    `(,pred ,a)))

(define encode-sub
  (lambda (a b)
    `((,sub ,a) ,b)))

(define encodeN
  (lambda (n)
    (if (zero? n) 'zero `(succ ,(encodeN (sub1 n))))))

(test "zero"
  (value-of
   'zero
   (empty-env))
  'zero)

(test "succ zero"
  (value-of
   '(succ zero)
   (empty-env))
  '(succ zero))

(test "add1"
  (value-of
   '(natrec (succ zero) (zero (succ zero)) (succ _ with y (succ y)))
   (empty-env))
  '(succ (succ zero)))

(test "plus 1 2"
  (value-of
   (encode-plus (encodeN 1) (encodeN 2))
   (empty-env))
   (encodeN 3))

(test "mult 2 3"
  (value-of
   (encode-mult (encodeN 2) (encodeN 3))
   (empty-env))
   (encodeN 6))

(test "fact 5"
  (value-of
   (encode-fact (encodeN 5))
   (empty-env))
   (encodeN 120))

(test "exp 2 3"
  (value-of
   (encode-exp (encodeN 2) (encodeN 3))
   (empty-env))
   (encodeN 8))

(test "pred 5"
  (value-of
   (encode-pred (encodeN 5))
   (empty-env))
   (encodeN 4))

(test "sub 5 3"
  (value-of
   (encode-sub (encodeN 5) (encodeN 3))
   (empty-env))
   (encodeN 2))

(test "sub 1 3"
  (value-of
   (encode-sub (encodeN 1) (encodeN 3))
   (empty-env))
   (encodeN 0))

(test "sub 5 5"
  (value-of
   (encode-sub (encodeN 5) (encodeN 5))
   (empty-env))
   (encodeN 0))
  
      
    