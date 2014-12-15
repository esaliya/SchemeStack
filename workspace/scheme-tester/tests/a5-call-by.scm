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

(define val-of-cbr
  (lambda (exp env)
    (pmatch exp
      [,b (guard (boolean? b)) b]
      [,n (guard (number? n)) n]
      [,x (guard (symbol? x)) (unbox (apply-env env x))]
      [(zero? ,n) (zero? (val-of-cbr n env))]
      [(sub1 ,n) (sub1 (val-of-cbr n env))]
      [(* ,n1 ,n2) (* (val-of-cbr n1 env) (val-of-cbr n2 env))]
      [(lambda (,x) ,body) (closure-cbr x body env)]
      [(if ,test ,conseq ,alt) (if (val-of-cbr test env)
                                   (val-of-cbr conseq env)
                                   (val-of-cbr alt env))]
      [(begin2 ,e1 ,e2) (begin (val-of-cbr e1 env) (val-of-cbr e2 env))]
      [(random ,n) (random n)]
      [(set! ,x ,rhs) (set-box! (apply-env env x) (val-of-cbr rhs env))] 
      [(let ((,x ,a)) ,body) (val-of-cbr body (extend-env env x (if (symbol? a) 
                                                              (apply-env env a) 
                                                              (box (val-of-cbr a env)))))]
      ;; this little improvement will make it possible to specify whether i want to 
      ;; pass the reference or not :D
      [(,rator (& ,rand)) (guard (symbol? rand)) (apply-proc (val-of-cbr rator env)
                                  (apply-env env rand))]
      [(,rator ,rand) (apply-proc (val-of-cbr rator env)
                                  (box (val-of-cbr rand env)))])))

(define empty-env
  (lambda ()
    (lambda (y)
      (error 'empty-env "unbound variable ~s" y))))

(define extend-env
  (lambda (env x a)
    (lambda (y) (if (eq? x y) a (apply-env env y)))))

(define apply-env
  (lambda (env x)
    (env x)))

(define apply-proc
  (lambda (p a)
    (p a)))

;; Closure for the call-by-reference
(define closure-cbr
  (lambda (x body env)
    (lambda (a) (val-of-cbr body (extend-env env x a)))))

; this will change the value of x eventhough it is set inside the inner
; lambda where we set the value of y to be 4. Since we passed the reference
; to the inner lambda we eventually have changed the value of x as well
(test "ref-pass"
  (val-of-cbr '((lambda (x) (begin2 ((lambda (y) (set! y 4)) (& x)) x)) 7) (empty-env))   
  4)

(test "val-pass"
  (val-of-cbr '((lambda (x) (begin2 ((lambda (y) (set! y 4)) x) x)) 7) (empty-env))  
  7)





