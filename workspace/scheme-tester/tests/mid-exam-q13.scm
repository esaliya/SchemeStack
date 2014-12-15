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
      [(let*2 ([,x1 ,e1] [,x2 ,e2]) ,body) (let ([env (extend-env x1 (value-of e1 env) env)])
                                             (value-of body (extend-env x2 (value-of e2 env) env)))]
;;      [(let*2 ([,x1 ,e1] [,x2 ,e2]) ,body) (let ([e1 (value-of e1 env)] [e2 (value-of e2 env)])
;;                                             (value-of body (extend-env x1 e1 (extend-env x2 e2 env))))]
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
   '(let*2 ([x 3] [y x])
      (* x y))
   (empty-env))
  9)

;;(test "data structural: let-e"
;;  (value-of
;;   '(let ([y (* 3 4)])
;;      ((lambda (x) (* x y)) (sub1 (* y y))))
;;   (empty-env))
;;  1716)

