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
      [,x (guard (boolean? x)) x]
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

(test "data structural: boolean-a"
  (value-of '(if #t #f #t) (empty-env))
  #f)

(test "data structural: boolean-b"
  (value-of '(if (zero? 10) #f #t) (empty-env))
  #t)

(test "data structural: *-a"
  (value-of '(* (* 4 3) (* 5 9)) (empty-env))
  540)

(test "data structural: *-b"
  (value-of '(* (* (* (* (* 1 2) 3) 4) 5) 6) (empty-env))
  720)

(test "data structural: number-a"
  (value-of '10 (empty-env))
  10)

(test "data structural: number-b"
  (value-of '2 (empty-env))
  2)

(test "data structural: lambda-a"
  (value-of '((lambda (x) x) 5) (empty-env))
  5)

(test "data structural: lambda-b"
  (value-of '((((lambda (x) 
                (lambda (y) 
                  (lambda (z)
                    (* x (* y z))))) 5)4)3) (empty-env))
  60)

(test "data structural: application-a"
  (value-of '((lambda (x) (* x x)) 
              ((lambda (x) (sub1 x)) 4)) (empty-env))
  9)

(test "data structural: application-b"
  (value-of '(((lambda (x) (lambda (y) (* x y))) 3) 
              ((lambda (x) (sub1 x)) 4)) (empty-env))
  9)

(test "data structural: if-a"
  (value-of '(if #f #f #t) (empty-env))
  #t)

(test "data structural: if-b"
  (value-of '(if (zero? 0) #t #f) (empty-env))
  #t)

(test "data structural: zero-a"
  (value-of '(zero? 0) (empty-env))
  #t)

(test "data structural: zero-b"
  (value-of '(zero? 2) (empty-env))
  #f)

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

(test "higer order: boolean-a"
  (value-of '(if #t #f #t) (empty-env))
  #f)

(test "higer order: boolean-b"
  (value-of '(if (zero? 10) #f #t) (empty-env))
  #t)

(test "higer order: *-a"
  (value-of '(* (* 4 3) (* 5 9)) (empty-env))
  540)

(test "higer order: *-b"
  (value-of '(* (* (* (* (* 1 2) 3) 4) 5) 6) (empty-env))
  720)

(test "higer order: number-a"
  (value-of '10 (empty-env))
  10)

(test "higer order: number-b"
  (value-of '2 (empty-env))
  2)

(test "higer order: lambda-a"
  (value-of '((lambda (x) x) 5) (empty-env))
  5)

(test "higer order: lambda-b"
  (value-of '((((lambda (x) 
                (lambda (y) 
                  (lambda (z)
                    (* x (* y z))))) 5)4)3) (empty-env))
  60)

(test "higer order: application-a"
  (value-of '((lambda (x) (* x x)) 
              ((lambda (x) (sub1 x)) 4)) (empty-env))
  9)

(test "higer order: application-b"
  (value-of '(((lambda (x) (lambda (y) (* x y))) 3) 
              ((lambda (x) (sub1 x)) 4)) (empty-env))
  9)

(test "higer order: if-a"
  (value-of '(if #f #f #t) (empty-env))
  #t)

(test "higer order: if-b"
  (value-of '(if (zero? 0) #t #f) (empty-env))
  #t)

(test "higer order: zero-a"
  (value-of '(zero? 0) (empty-env))
  #t)

(test "higer order: zero-b"
  (value-of '(zero? 2) (empty-env))
  #f)


;----------------------------------------------------------------
; Extra-Hard Brainteaser
;----------------------------------------------------------------

(define base
  (lambda (t)
    `(0 . ,t)))
 
(define stuff
  (lambda (w)
    `(,w . macht-nicht)))
 
(define grow
  (lambda (f)
    (lambda (c)
      (let ((c^ (f (cdr c))))
        (set-car! c^ (+ (car c) (car c^)))
        c^))))

(define rembersum*even
  (lambda (ls)
    (cond
      [(null? ls) (base '())]
      [(pair? (car ls))
       ((grow (lambda (a) ((grow (lambda (d) (base (cons a d)))) (rembersum*even (cdr ls)))))
        (rembersum*even (car ls)))]
      [(and (number? (car ls)) (even? (car ls)))
       ((grow (lambda (__) (rembersum*even (cdr ls)))) (stuff (car ls)))]
      [else ((grow (lambda (d) (base (cons (car ls) d)))) (rembersum*even (cdr ls)))])))

;----------------------------------------------------------------
; Test cases for extra-hard brainteaser
;----------------------------------------------------------------
(test "rembersum*even: a"
  (rembersum*even '(5 (((7)) 9) 11))
  '(0 5 (((7)) 9) 11))

(test "rembersum*even: b"
  (rembersum*even  '(2 3 (8 (c 6 7) 4 8 #t) 8 () 2 9))
  '(38 3 ((c 7) #t) () 9))

(test "rembersum*even: c"
  (rembersum*even  '())
  '(0))

(test "rembersum*even: d"
  (rembersum*even  '(1))
  '(0 1))

(test "rembersum*even: e"
  (rembersum*even  '(2 1 3 4))
  '(6 1 3))

(test "rembersum*even: f"
  (rembersum*even  '(2 (1 3) (4 1)))
  '(6 (1 3) (1)))

(test "rembersum*even: g"
  (rembersum*even  '(0 (1 (3 2)) (4 1)))
  '(6 (1 (3)) (1)))


;----------------------------------------------------------------
; Super Mega-Hard Brainteaser
;----------------------------------------------------------------

(define lbase
  (lambda (t)
    `(() . ,t)))
 
(define lstuff
  (lambda (w)
    `((,w) . macht-nicht)))
 
(define lgrow
  (lambda (f)
    (lambda (c)
      (let ((c^ (f (cdr c))))
        (set-car! c^ (append (car c) (car c^)))
        c^))))

(define remberlist*even
  (lambda (ls)
    (cond
      [(null? ls) (lbase '())]
      [(pair? (car ls))
       ((lgrow (lambda (a) ((lgrow (lambda (d) (lbase (cons a d)))) (remberlist*even (cdr ls)))))
        (remberlist*even (car ls)))]
      [(and (number? (car ls)) (even? (car ls)))
       ((lgrow (lambda (__) (remberlist*even (cdr ls)))) (lstuff (car ls)))]
      [else ((lgrow (lambda (d) (lbase (cons (car ls) d)))) (remberlist*even (cdr ls)))])))

;----------------------------------------------------------------
; Test cases for super mega-hard brainteaser
;----------------------------------------------------------------
(test "remberlist*even: a"
  (remberlist*even '(5 (((7)) 9) 11))
  '(() 5 (((7)) 9) 11))

(test "remberlist*even: b"
  (remberlist*even  '(2 3 (8 (5 6 7) 4 8 7) 8 () 2 9))
  '((2 8 6 4 8 8 2) 3 ((5 7) 7) () 9))

(test "remberlist*even: c"
  (remberlist*even  '())
  '(()))

(test "remberlist*even: d"
  (remberlist*even  '(1))
  '(() 1))

(test "remberlist*even: e"
  (remberlist*even  '(2 1 3 4))
  '((2 4) 1 3))

(test "remberlist*even: f"
  (remberlist*even  '(2 (1 3) (4 1)))
  '((2 4) (1 3) (1)))

(test "remberlist*even: g"
  (remberlist*even  '(0 (1 (3 2)) (4 1)))
  '((0 2 4) (1 (3)) (1)))