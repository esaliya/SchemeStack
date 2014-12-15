;;; miniKanren interpreter for a subset of Scheme

(load "a12-mkdefs.scm")
(load "pmatch.scm")

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

(define parse
  (lambda (expr)
    (pmatch expr
      [,n (guard (integer? n)) `(int ,(build-num n))]
      [,x (guard (symbol? x)) `(var ,x)]
      [(zero? ,e) `(zero? ,(parse e))]
      [(* ,e1 ,e2) `(* ,(parse e1) ,(parse e2))]
      [(sub1 ,e) `(sub1 ,(parse e))]
      [(if ,test ,conseq ,alt)
       `(if ,(parse test) ,(parse conseq) ,(parse alt))]        
      [(lambda (,id) ,body)
       `(lambda (,id) ,(parse body))]
      [(,rator ,rand)
       `(app ,(parse rator) ,(parse rand))]
      [else (error "invalid language construct ~s" expr)])))

(define value-ofo
  (lambda (exp env out)
    (exist (rator-val rand-val x body rator rand)
      (conde
        [(== `(lambda (,x) ,body) exp) (== (closure x body env) out)]
        [(== `(var ,x) exp) (apply-envo env x out)]
        [(== `(app ,rator ,rand) exp)
         (value-ofo rator env rator-val)
         (value-ofo rand env rand-val)
         (apply-proco rator-val rand-val out)]))))

(define empty-env
  (lambda ()
    `(empty-env)))

(define extend-env
  (lambda (y a env^)
    `(extend-env ,y ,a ,env^)))

(define apply-envo
  (lambda (env x out)
    (exist (y env^ a)
      (conde
        [(== `(empty-env) env) (== #f #t)]
        [(== `(extend-env ,y ,a ,env^) env)
         (conde
           [(== y x) (== a out)]
           [(=/= y x) (apply-envo env^ x out)])]))))

(define closure
  (lambda (id body env)
    `(closure ,id ,body ,env)))

(define apply-proco
  (lambda (p a out)
    (exist (id body env)
      (conde
        [(== `(closure ,id ,body ,env) p)
         (value-ofo body (extend-env id a env) out)]))))

(define value-ofo
  (lambda (exp env out)
    (exist (rator-val rand-val x body rator rand n res e res1)
      (conde
        [(== `(int ,n) exp) (== `(v-int ,n) out)]
        [(== `(lambda (,x) ,body) exp) (== (closure x body env) out)]
        [(== `(var ,x) exp) (apply-envo env x out)]
        [(== `(sub1 ,e) exp)
         (== `(v-int ,n) res)
         (== `(v-int ,res1) out)
         (value-ofo e env res)
         (minuso n (build-num 1) res1)]
        [(== `(app ,rator ,rand) exp)
         (value-ofo rator env rator-val)
         (value-ofo rand env rand-val)
         (apply-proco rator-val rand-val out)]))))

(define value-ofo
  (lambda (exp env out)
    (exist (rator-val rand-val x body rator rand n n1 n2 res e e1 e2 b t c a)
      (conde
        [(== `(int ,n) exp) (== `(v-int ,n) out)]
        [(== `(lambda (,x) ,body) exp) (== (closure x body env) out)]
        [(== `(var ,x) exp) (apply-envo env x out)]
        [(== `(zero? ,e) exp)
         (conde
           [(== '() n) (== `(v-bool #t) out)]
           [(poso n) (== `(v-bool #f) out)])
         (value-ofo e env `(v-int ,n))]
        [(== `(sub1 ,e) exp)
         (== `(v-int ,res) out)
         (value-ofo e env `(v-int ,n))
         (minuso n (build-num 1) res)]
        [(== `(* ,e1 ,e2) exp)
         (== `(v-int ,res) out)
         (value-ofo e1 env `(v-int ,n1))
         (value-ofo e2 env `(v-int ,n2))         
         (*o n1 n2 res)]
        [(== `(app ,rator ,rand) exp)
         (value-ofo rator env rator-val)
         (value-ofo rand env rand-val)
         (apply-proco rator-val rand-val out)]
        [(== `(if ,t ,c ,a) exp)
         (value-ofo t env `(v-bool ,b))
         (conde
           [(== b #t) (value-ofo c env out)]
           [(== b #f) (value-ofo a env out)])]))))

(test "value-ofo-1"
  (run* (q)
    (value-ofo `(int ,(build-num 5)) (empty-env) q))
  '((v-int (1 0 1))))

(test "value-ofo-2"
  (run* (q)
    (value-ofo `(sub1 (int ,(build-num 5))) (empty-env) q))
  '((v-int (0 0 1))))

(test "value-ofo-3"
  (run* (q)
    (value-ofo `(sub1 (sub1 (int ,(build-num 5)))) (empty-env) q))
  '((v-int (1 1))))

(test "value-ofo-4"
  (run* (q)
    (value-ofo '(lambda (y) (var y)) (empty-env) q))
  '((closure y (var y) (empty-env))))

(test "value-ofo-5"
  (run 5 (q)
    (value-ofo q (empty-env) `(v-int ,(build-num 5))))
  '((int (1 0 1))
    (* (int (1)) (int (1 0 1)))
    (* (int (1 0 1)) (int (1)))
    (sub1 (int (0 1 1)))
    (if (zero? (int ())) (int (1 0 1)) _.0)))

(test "value-ofo-6"
  (run* (q)
    (value-ofo '(app (lambda (x) (lambda (y) (var x))) (lambda (y) (var y))) (empty-env) q))
  '((closure y (var x) (extend-env x (closure y (var y) (empty-env)) (empty-env)))))

(test "value-ofo-7"
  (run 10 (q)
    (exist (x y out)
      (value-ofo `(app ,x ,y) (empty-env) out)
      (== `(,x ,y ,out) q)))
  '(((lambda (_.0) (int _.1)) (int _.2) (v-int _.1))
    ((lambda (_.0) (lambda (_.1) _.2))
     (int _.3)
     (closure _.1 _.2 (extend-env _.0 (v-int _.3) (empty-env))))
    ((lambda (_.0) (int _.1)) (lambda (_.2) _.3) (v-int _.1))
    ((lambda (_.0) (var _.0)) (int _.1) (v-int _.1))
    ((lambda (_.0) (lambda (_.1) _.2))
     (lambda (_.3) _.4)
     (closure
      _.1
      _.2
      (extend-env _.0 (closure _.3 _.4 (empty-env)) (empty-env))))
    ((lambda (_.0) (zero? (int ()))) (int _.1) (v-bool #t))
    ((lambda (_.0) (var _.0))
     (lambda (_.1) _.2)
     (closure _.1 _.2 (empty-env)))
    ((lambda (_.0) (zero? (int (_.1 . _.2))))
     (int _.3)
     (v-bool #f))
    ((lambda (_.0) (sub1 (int (1)))) (int _.1) (v-int ()))
    ((lambda (_.0) (zero? (int ())))
     (lambda (_.1) _.2)
     (v-bool #t))))

(test "value-ofo-8"
  (run 1 (q)
    (value-ofo q (empty-env) `(v-int ,(build-num 5)))    
    (== `(sub1 (sub1 (sub1 (int ,(build-num 8))))) q))
  '((sub1 (sub1 (sub1 (int (0 0 0 1)))))))

(test "value-ofo-!"
  (run 1 (q)
    (value-ofo (parse '(((lambda (!)
                           (lambda (n)
                             (if (zero? n)
                                 1
                                 (* ((! !) (sub1 n)) n))))
                         (lambda (!)
                           (lambda (n)
                             (if (zero? n)
                                 1
                                 (* ((! !) (sub1 n)) n)))))
                        5))
               (empty-env)
               q))
  '((v-int (0 0 0 1 1 1 1))))
