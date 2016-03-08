;;----------------------------------
;; B521 - Assignment 4
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


;-------------------------------------------------------------------------
; Interpreter with both lambda and d-lambda support
;-------------------------------------------------------------------------
(define value-of
  (lambda (e env)
    (pmatch e
      [,x (guard (symbol? x)) (apply-env env x)]
      [,x (guard (boolean? x)) x]
      [(lambda (,x) ,body) (closure x body env)]
      [(d-lambda (,x) ,body) (d-closure x body)]
      [,n (guard (number? n)) n]
      [(* ,exp-1 ,exp-2) (* (value-of exp-1 env) (value-of exp-2 env))]
      [(let ,s ,body) (value-of body (extend-env-with-list s env))]
      [(sub1 ,exp) (sub1 (value-of exp env))]
      [(if ,con ,kt, kf) (if (value-of con env) (value-of kt env) (value-of kf env))]
      [(zero? ,exp) (zero? (value-of exp env))]
      [(,rator ,rand) (apply-proc (value-of rator env) (value-of rand env) env)])))


;---------------------------------------------------------------------------
; Helper function to extend the environment with a list of name/value pairs
;---------------------------------------------------------------------------
(define extend-env-with-list
  (lambda (s env)
    (cond
      [(null? s) env]
      [(not (null? (cdr s))) (extend-env-with-list (cdr s) (extend-env (caar s) (value-of (cadar s) env) env))]
      [else (extend-env (caar s) (value-of (cadar s) env) env)])))


;-------------------------------------------------------------------------
; Helper functions for environment based on data structure representation
;-------------------------------------------------------------------------
(define empty-env
  (lambda ()
    `(empty-env)))

(define extend-env
  (lambda (x a env)
    `(extend-env ,x ,a ,env)))

(define apply-env
  (lambda (env y)
    (pmatch env
      [(empty-env) (error 'empty-env "unbound variable ~s" y)]
      [(extend-env ,x ,a ,env) (if (eq? y x) a (apply-env env y))])))


;----------------------------------------------------------------------
; Helper functions for procedures based on higher order representation
;----------------------------------------------------------------------
(define apply-proc
  (lambda (p a env^)
    (p a env^)))

(define closure
  (lambda (x body env)
    (lambda (a env^) (value-of body (extend-env x a env)))))
      
(define d-closure
  (lambda (x body)
    (lambda (a env^) (value-of body (extend-env x a env^)))))
  


;----------------------------------------------------------------
; Test definitions for static and dynamic scoping
;----------------------------------------------------------------
(define let-static-a
  '(let ([x 2])
     (let ([f (lambda (e) x)])
       (let ([x 5])
         (f 0)))))

(define let-dynamic-a
  '(let ([x 2])
     (let ([f (d-lambda (e) x)])
       (let ([x 5])
         (f 0)))))

(define let-static-b
  '(let ([x 2])
     (let ([f (lambda (e) (* e x))])
       (let ([x 5])
         (f x)))))

(define let-dynamic-b
  '(let ([x 2])
     (let ([f (d-lambda (e) (* e x))])
       (let ([x 5])
         (f x)))))


;----------------------------------------------------------------
; Test cases for higher order helpers
;----------------------------------------------------------------
(printf "\n=================================================\nTests for Higher Order Helpers\n=================================================\n")

(test "fact"
  (value-of '((let ([! (lambda (!)
              (lambda (n)
                (if (zero? n)
                    1
                    (* n ((! !) (sub1 n))))))])
     (! !))
   5) (empty-env))
  120)

(test "let-a"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 6)))
   (empty-env))
  60)

(test "let-b"
  (value-of
   '(let ([x (* 2 3)])
      (let ([y (sub1 x)])
        (* x y)))
   (empty-env))
  30)

(test "let-c"
  (value-of
   '(let ([x (* 2 3)])
      (let ([x (sub1 x)])
        (* x x)))
   (empty-env))
  25)

(test "let-d"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 (* y (sub1 y)))))
   (empty-env))
  1572)

(test "let-e"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 (* y y))))
   (empty-env))
  1716)

(test "let-f"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 (sub1 y))))
   (empty-env))
  120)

(test "let-g"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 ((lambda (x) (* x x)) (sub1 y)))))
   (empty-env))
  1440)

(test "boolean-a"
  (value-of '(if #t #f #t) (empty-env))
  #f)

(test "boolean-b"
  (value-of '(if (zero? 10) #f #t) (empty-env))
  #t)

(test "*-a"
  (value-of '(* (* 4 3) (* 5 9)) (empty-env))
  540)

(test "*-b"
  (value-of '(* (* (* (* (* 1 2) 3) 4) 5) 6) (empty-env))
  720)

(test "number-a"
  (value-of '10 (empty-env))
  10)

(test "number-b"
  (value-of '2 (empty-env))
  2)

(test "lambda-a"
  (value-of '((lambda (x) x) 5) (empty-env))
  5)

(test "lambda-b"
  (value-of '((((lambda (x) 
                (lambda (y) 
                  (lambda (z)
                    (* x (* y z))))) 5)4)3) (empty-env))
  60)

(test "application-a"
  (value-of '((lambda (x) (* x x)) 
              ((lambda (x) (sub1 x)) 4)) (empty-env))
  9)

(test "application-b"
  (value-of '(((lambda (x) (lambda (y) (* x y))) 3) 
              ((lambda (x) (sub1 x)) 4)) (empty-env))
  9)

(test "if-a"
  (value-of '(if #f #f #t) (empty-env))
  #t)

(test "if-b"
  (value-of '(if (zero? 0) #t #f) (empty-env))
  #t)

(test "zero-a"
  (value-of '(zero? 0) (empty-env))
  #t)

(test "zero-b"
  (value-of '(zero? 2) (empty-env))
  #f)


(printf "-------------------------------------------------\nTests for Static/Dynamic Binding\n-------------------------------------------------\n")

(test "let-test-static-a"
  (value-of let-static-a (empty-env))
  2)

(test "let-test-dynamic-a"
  (value-of let-dynamic-a (empty-env))
  5)

(test "let-test-static-b"
  (value-of let-static-b (empty-env))
  10)

(test "let-test-dynamic-b"
  (value-of let-dynamic-b (empty-env))
  25)


;-------------------------------------------------------------------------
; Helper functions for procedures based on data structural representation
;-------------------------------------------------------------------------
(define apply-proc
  (lambda (p a env^)
    (pmatch p
      [(closure ,x ,body) (value-of body (extend-env x a env^))]
      [(closure ,x ,body, env) (value-of body (extend-env x a env))]))) 

(define closure
  (lambda (x body env)
    `(closure ,x ,body ,env)))

(define d-closure
  (lambda (x body)
    `(closure ,x ,body)))
  



;----------------------------------------------------------------
; Test cases for data structural helpers
;----------------------------------------------------------------
(printf "\n\n\n=================================================\nTests for Data Structural Helpers\n=================================================\n")

(test "fact"
  (value-of '((let ([! (lambda (!)
              (lambda (n)
                (if (zero? n)
                    1
                    (* n ((! !) (sub1 n))))))])
     (! !))
   5) (empty-env))
  120)

(test "let-a"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 6)))
   (empty-env))
  60)

(test "let-b"
  (value-of
   '(let ([x (* 2 3)])
      (let ([y (sub1 x)])
        (* x y)))
   (empty-env))
  30)

(test "let-c"
  (value-of
   '(let ([x (* 2 3)])
      (let ([x (sub1 x)])
        (* x x)))
   (empty-env))
  25)

(test "let-d"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 (* y (sub1 y)))))
   (empty-env))
  1572)

(test "let-e"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 (* y y))))
   (empty-env))
  1716)

(test "let-f"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 (sub1 y))))
   (empty-env))
  120)

(test "let-g"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 ((lambda (x) (* x x)) (sub1 y)))))
   (empty-env))
  1440)

(test "boolean-a"
  (value-of '(if #t #f #t) (empty-env))
  #f)

(test "boolean-b"
  (value-of '(if (zero? 10) #f #t) (empty-env))
  #t)

(test "*-a"
  (value-of '(* (* 4 3) (* 5 9)) (empty-env))
  540)

(test "*-b"
  (value-of '(* (* (* (* (* 1 2) 3) 4) 5) 6) (empty-env))
  720)

(test "number-a"
  (value-of '10 (empty-env))
  10)

(test "number-b"
  (value-of '2 (empty-env))
  2)

(test "lambda-a"
  (value-of '((lambda (x) x) 5) (empty-env))
  5)

(test "lambda-b"
  (value-of '((((lambda (x) 
                (lambda (y) 
                  (lambda (z)
                    (* x (* y z))))) 5)4)3) (empty-env))
  60)

(test "application-a"
  (value-of '((lambda (x) (* x x)) 
              ((lambda (x) (sub1 x)) 4)) (empty-env))
  9)

(test "application-b"
  (value-of '(((lambda (x) (lambda (y) (* x y))) 3) 
              ((lambda (x) (sub1 x)) 4)) (empty-env))
  9)

(test "if-a"
  (value-of '(if #f #f #t) (empty-env))
  #t)

(test "if-b"
  (value-of '(if (zero? 0) #t #f) (empty-env))
  #t)

(test "zero-a"
  (value-of '(zero? 0) (empty-env))
  #t)

(test "zero-b"
  (value-of '(zero? 2) (empty-env))
  #f)


(printf "-------------------------------------------------\nTests for Static/Dynamic Binding\n-------------------------------------------------\n")

(test "let-test-static-a"
  (value-of let-static-a (empty-env))
  2)

(test "let-test-dynamic-a"
  (value-of let-dynamic-a (empty-env))
  5)

(test "let-test-static-b"
  (value-of let-static-b (empty-env))
  10)

(test "let-test-dynamic-b"
  (value-of let-dynamic-b (empty-env))
  25)

