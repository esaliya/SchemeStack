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

(define value-of
  (lambda (e env)
    (pmatch e
      [,x (guard (symbol? x)) (apply-env env x)]
      [(lambda (,x) ,body) (closure x body env)]
      [,n (guard (number? n)) n]
      [(* ,exp-1 ,exp-2) (* (value-of exp-1 env) (value-of exp-2 env))]      
      [(let ,s ,body) (value-of body (extend-env-with-list s env))]
      [(sub1 ,exp) (sub1 (value-of exp env))]
      [(if ,con ,kt, kf) (if (value-of con env) (value-of kt env) (value-of kf env))]
      [(zero? ,exp) (zero? (value-of exp env))]
      [(,rator ,rand) (apply-proc (value-of rator env) (value-of rand env))])))

(define extend-env-with-list
  (lambda (s env)
    (cond
      [(null? s) env]
      [(not (null? (cdr s))) (extend-env-with-list (cdr s) (extend-env (caar s) (value-of (cadar s) env) env))]
      [else (extend-env (caar s) (value-of (cadar s) env) env)])))

(define apply-proc
  (lambda (p a)
    (p a)))

(define closure
  (lambda (x body env)
    (lambda (a) (value-of body (extend-env x a env)))))

;----------------------------------------------------------------
; Helper functions based on data structure representation
;----------------------------------------------------------------

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

;----------------------------------------------------------------
; Test cases for data structural helpers
;----------------------------------------------------------------

(test "data structural: let-a"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 6)))
   (empty-env))
  60)
 
(test "data structural: let-b"
  (value-of
   '(let ([x (* 2 3)])
      (let ([y (sub1 x)])
        (* x y)))
   (empty-env))
  30)
 
(test "data structural: let-c"
  (value-of
   '(let ([x (* 2 3)])
      (let ([x (sub1 x)])
        (* x x)))
   (empty-env))
  25)

(test "data structural: let-d"
      (value-of
       '(let ([y (* 3 4)])
          ((lambda (x) (* x y)) (sub1 (* y (sub1 y)))))
       (empty-env))
      1572)

(test "data structural: let-e"
      (value-of
       '(let ([y (* 3 4)])
          ((lambda (x) (* x y)) (sub1 (* y y))))
       (empty-env))
      1716)

(test "data structural: let-f"
      (value-of
       '(let ([y (* 3 4)])
          ((lambda (x) (* x y)) (sub1 (sub1 y))))
       (empty-env))
      120)

(test "data structural: let-g"
      (value-of
       '(let ([y (* 3 4)])
          ((lambda (x) (* x y)) (sub1 ((lambda (x) (* x x)) (sub1 y)))))
       (empty-env))
      1440)

;----------------------------------------------------------------
; The helper functions based on higher order representation
;----------------------------------------------------------------

(define extend-env
  (lambda (x a env)
    (lambda (y)
      (if (eq? x y) a (apply-env env y)))))

(define empty-env
  (lambda ()
    (lambda (y)
      (error 'empty-env "unbound variable ~s" y))))

(define apply-env
  (lambda (env x)
    (env x)))

;----------------------------------------------------------------
; Test cases for higher order helpers
;----------------------------------------------------------------

(test "higher order: let-a"
  (value-of
   '(let ([y (* 3 4)])
      ((lambda (x) (* x y)) (sub1 6)))
   (empty-env))
  60)
 
(test "higher order: let-b"
  (value-of
   '(let ([x (* 2 3)])
      (let ([y (sub1 x)])
        (* x y)))
   (empty-env))
  30)
 
(test "higher order: let-c"
  (value-of
   '(let ([x (* 2 3)])
      (let ([x (sub1 x)])
        (* x x)))
   (empty-env))
  25)

(test "higher order: let-d"
      (value-of
       '(let ([y (* 3 4)])
          ((lambda (x) (* x y)) (sub1 (* y (sub1 y)))))
       (empty-env))
      1572)

(test "higher order: let-e"
      (value-of
       '(let ([y (* 3 4)])
          ((lambda (x) (* x y)) (sub1 (* y y))))
       (empty-env))
      1716)

(test "higher order: let-f"
      (value-of
       '(let ([y (* 3 4)])
          ((lambda (x) (* x y)) (sub1 (sub1 y))))
       (empty-env))
      120)

(test "higher order: let-g"
      (value-of
       '(let ([y (* 3 4)])
          ((lambda (x) (* x y)) (sub1 ((lambda (x) (* x x)) (sub1 y)))))
       (empty-env))
      1440)


