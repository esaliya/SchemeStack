;;----------------------------------
;; B521 - Assignment 5
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    0002560797
;; Email: sekanaya@indiana.edu
;;----------------------------------

;=================================================Part I==================================================

(define map
  (lambda (f l)
    (cond
      [(null? l) '()]
      [else (cons (f (car l)) (map f (cdr l)))])))

(let ([l '(a b c)])
  (map (lambda (x) (cons x l)) l))

;-------------------------------------------------------------------------------------------------------------
;Value under lexical scope is 
;((a a b c) (b a b c) (c a b c))
;
;The key thing in lexical scoping is that we remember the environment upon which a function is defined. Then
;for any look up we use the particular environment rather the runtime environment.
;
;-------------------------------------------------------------------------------------------------------------
;I will assume that we start with an empty environment E0. I will also assume that the definition of 'map'
;has extended it with a function as given below. The extended environment is denoted as E1.
;
;(lambda (p q) (value-of map-body (extend-env (extend-env E1 l q) f p)))
;
;Thus, E1 becomes,
;
;E1: map <-- (lambda (p q) (value-of map-body (extend-env (extend-env E1 l q) f p))) | E0
;
;Note. 1.) 'map-body' refers to the body of the 'map' definition.
;      2.) The function denoted by 'map' in E1 has a reference to E1 itself. I am not sure if this is the way
;          how 'define' does it actually. Anyway, this facilitates recursion when 'map' calls 'map' inside 
;          'map-body'.
;-------------------------------------------------------------------------------------------------------------
;Now we find an 'let' expression and try to evaluate it under E1
;       
;I) Extend E1 with l <-- (a b c). Now we have a new environment, E2,
;   E2: l <-- (a b c) | E1
;       
;II) Evaluate let-body under E2.    
;
;      I) Get the value-of map, which is directly looked up in E2 and resolves to the 'map' function.
;     II) Get the value-of '(lambda (x) (cons x l))'. This results in another function as given below.
;         (lambda (y) (value-of anon-body (extend-env E2 x y)))
;         Note. 'anon-body' refers to '(cons x l)'
;       
;    III) Get the value-of 'l', which again is a direct look up in E2 and resolves to (a b c).
;     IV) Now apply 'map' on the above two values.
;
;III) Applying 'map' reduces to evaluating 'map-body' under its defined environment (say Em), i.e.,
;     (value-of map-body Em) where,
;     Em: f <-- (lambda (y) (value-of anon-body (extend-env E2 x y))) | l <-- (a b c) | E1
;
;       I) First look up 'l' in Em and check whether it's null or not. Since 'l' is not null in Em we
;          go for the next condition, i.e. else.
;      II) Next we apply 'f' on '(car l)' and 'map' on 'f' and '(cdr l)'. These are cons together and returned.
;          We can find what 'map' is since Em has E1 in it.
;          Note. It's trivial to undrestand '(car l)' is 'a' and '(cdr l)' is '(b c)' in this case.
;
;IV) Applying 'f' on '(car l)' means to evaluate 'anon-body' under its defined environment (say Ea), i.e.,
;    (value-of anon-body Ea) where,
;    Ea: x <-- a | E2
;
;      I) Look up 'x' and 'l' in Ea, which turns out to be 'a' and '(a b c)'.
;     II) Return the cons of those two, i.e. '(a a b c)'.
;
;V) Next applying 'map' on 'f' and '(cdr l)' means to evaluate 'map-body' under its defined environment, Em.
;   This is again the step III) defined above except that now we get Em as,
;   Em: f <-- (lambda (y) (value-of anon-body (extend-env E2 x y))) | l <-- (b c) | E1
;
;   Then we go into the same step IV) defined above with Ea being defined as,
;   Ea: x <-- b | E2
;
;   The returned value of step IV) is now '(b a b c)'
;
;VI) The same cycle repeats another time with Em and Ea as defined below.
;    Em: f <-- (lambda (y) (value-of anon-body (extend-env E2 x y))) | l <-- (c) | E1
;    Ea: x <-- c | E2
;    
;    The returned value in this case is (c a b c)
;
;VII) We again go to step III), but in this case we get Em as,
;     Em: f <-- (lambda (y) (value-of anon-body (extend-env E2 x y))) | l <-- () | E1
;     Note. 'l' is now null.
;
;     Now, our (null? l) is true and we return an empty list instead of going to step IV). This ends the 
;     recursion.
;
;VIII) Now we can go down the frames stack, which results in the following,
;      (cons '(a a b c) (cons '(b a b c) (cons '(c a b c) '())))
;
;      This is equal to,
;      ((a a b c) (b a b c) (c a b c)) which is the final result we expected.
;-------------------------------------------------------------------------------------------------------------
;
;
;-------------------------------------------------Dynamic Scope-----------------------------------------------
;Value under dynamic scope is 
;((a a b c) (b b c) (c c))
;
;The key thing in dynamic scoping is that we DON'T remember the environment upon which a function is defined. 
;Instead, the function depends upon an environment given to it at its application time. The particular 
;environment is in fact the runtime environment.
;-------------------------------------------------------------------------------------------------------------
;I will assume that we start with an empty environment E0. I will also assume that the definition of 'map'
;has extended it with a function as given below. The extended environment is denoted as E1.
;
;(lambda (p q env^) (value-of map-body (extend-env (extend-env env^ l q) f p)))
;
;Thus, E1 becomes,
;
;E1: map <-- (lambda (p q env^) (value-of map-body (extend-env (extend-env env^ l q) f p))) | E0
;
;Note. 1.) 'map-body' refers to the body of the 'map' definition.
;      2.) 'env^' is the environment given at the application time of the function.
;-------------------------------------------------------------------------------------------------------------
;;Now we find an 'let' expression and try to evaluate it under E1
;       
;I) Extend E1 with l <-- (a b c). Now we have a new environment, E2,
;   E2: l <-- (a b c) | E1
;       
;II) Evaluate let-body under E2.    
;
;      I) Get the value-of map, which is directly looked up in E2 and resolves to the 'map' function.
;     II) Get the value-of '(lambda (x) (cons x l))'. This results in another function as given below.
;         (lambda (y env^) (value-of anon-body (extend-env env^ x y)))
;         Note. 'anon-body' refers to '(cons x l)'
;       
;    III) Get the value-of 'l', which again is a direct look up in E2 and resolves to (a b c).
;     IV) Now apply 'map' on the above two values.
;
;III) Applying 'map' reduces to evaluating 'map-body' under an extended environment of E2 (say Em), i.e.,
;     (value-of map-body Em) where,
;     Em: f <-- (lambda (y env^) (value-of anon-body (extend-env env^ x y))) | l <-- (a b c) | E2
;
;       I) First look up 'l' in Em and check whether it's null or not. Since 'l' is not null in Em we
;          go for the next condition, i.e. else.
;      II) Next we apply 'f' on '(car l)' and 'map' on 'f' and '(cdr l)'. These are cons together and returned.
;          We can find what 'map' is since Em has E1 in it.
;          Note. It's trivial to undrestand '(car l)' is 'a' and '(cdr l)' is '(b c)' in this case.
;
;IV) Applying 'f' on '(car l)' (relates to III) II))means to evaluate 'anon-body' under an extended environment 
;    of Em (say Ea), i.e.,
;    (value-of anon-body Ea) where,
;    Ea: x <-- a | Em
;
;      I) Look up 'x' and 'l' in Ea, which turns out to be 'a' and '(a b c)'.
;     II) Return the cons of those two, i.e. '(a a b c)'.
;
;V) Next applying 'map' on 'f' and '(cdr l)' (relates to III) II)) means to evaluate 'map-body' under an 
;   extended environment of Em (say E'm), i.e.,
;   (value-of map-body E'm) where,
;   E'm: f <-- (lambda (y env^) (value-of anon-body (extend-env env^ x y))) | l <-- (b c) | Em
;
;       I) First look up 'l' in E'm and check whether it's null or not. Since 'l' is not null in E'm we
;          go for the next condition, i.e. else.
;      II) Next we apply 'f' on '(car l)' and 'map' on 'f' and '(cdr l)'. These are cons together and returned.
;          We can find what 'map' is since E'm has E1 in it.
;          Note. It's trivial to undrestand '(car l)' is 'b' and '(cdr l)' is '(c)' in this case.
;
;VI) Applying 'f' on '(car l)' (relates to V) II)) means to evaluate 'anon-body' under an extended environment 
;    of E'm (say E'a), i.e.,
;    (value-of anon-body E'a) where,
;    E'a: x <-- b | E'm
;
;      I) Look up 'x' and 'l' in E'a, which turns out to be 'b' and '(b c)'.
;     II) Return the cons of those two, i.e. '(b b c)'.
;
;VII) Next applying 'map' on 'f' and '(cdr l)' (relates to V) II)) means to evaluate 'map-body' under an 
;   extended environment of E'm (say E''m), i.e.,
;   (value-of map-body E''m) where,
;   E''m: f <-- (lambda (y env^) (value-of anon-body (extend-env env^ x y))) | l <-- (c) | E'm
;
;       I) First look up 'l' in E''m and check whether it's null or not. Since 'l' is not null in E''m we
;          go for the next condition, i.e. else.
;      II) Next we apply 'f' on '(car l)' and 'map' on 'f' and '(cdr l)'. These are cons together and returned.
;          We can find what 'map' is since E''m has E1 in it.
;          Note. It's trivial to undrestand '(car l)' is 'c' and '(cdr l)' is '()' in this case.
;
;VIII) Applying 'f' on '(car l)' (relates to VII) II)) means to evaluate 'anon-body' under an extended environment 
;    of E''m (say E''a), i.e.,
;    (value-of anon-body E''a) where,
;    E''a: x <-- c | E''m
;
;      I) Look up 'x' and 'l' in E''a, which turns out to be 'c' and '(c)'.
;     II) Return the cons of those two, i.e. '(c c)'.
;
;IX) Next applying 'map' on 'f' and '(cdr l)' (relates to VII) II)) means to evaluate 'map-body' under an  
;   extended environment of E''m (say E'''m), i.e.,
;   (value-of map-body E'''m) where,
;   E'''m: f <-- (lambda (y env^) (value-of anon-body (extend-env env^ x y))) | l <-- () | E''m
;
;       I) First look up 'l' in E'''m and check whether it's null or not. Since 'l' is null in E'''m we
;          simply returns an empty list '()'.
;   This ends the recursion.
;
;X) Now we can see the stack frame to understand what is the final return value.
; 
;   final-val <-- (let ...)
;                     |
;                     (map ...)
;                         |
;                         (cons (f ...) (map ...))
;                                 |         |
;                             (a a b c)     (cons (f ...) (map ...))
;                                                   |         |
;                                                (b b c)      (cons (f ...) (map ...))
;                                                                     |         |
;                                                                   (c c)      ()
;   
;   Therefore, final-val is (cons '(a a b c) (cons '(b b c) (cons '(c c) '())))
;   
;   This is equal to,
;   ((a a b c) (b b c) (c c)) which is our final answer.
;-------------------------------------------------------------------------------------------------------------


;==============================================Part II================================================
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
; Call-by-value Interpreter
; ---------------------------------------------------------------
(define val-of-cbv
  (lambda (exp env)
    (pmatch exp
      [,b (guard (boolean? b)) b]
      [,n (guard (number? n)) n]
      [,x (guard (symbol? x)) (unbox (apply-env env x))]
      [(zero? ,n) (zero? (val-of-cbv n env))]
      [(sub1 ,n) (sub1 (val-of-cbv n env))]
      [(* ,n1 ,n2) (* (val-of-cbv n1 env) (val-of-cbv n2 env))]
      [(lambda (,x) ,body) (closure-cbv x body env)]
      [(if ,test ,conseq ,alt) (if (val-of-cbv test env)
                                   (val-of-cbv conseq env)
                                   (val-of-cbv alt env))]
      [(set! ,x ,rhs) (set-box! (apply-env env x) (val-of-cbr rhs env))]
      [(begin2 ,e1 ,e2) (begin (val-of-cbv e1 env) (val-of-cbv e2 env))]
      [(random ,n) (random n)]
      [(,rator ,rand) (apply-proc (val-of-cbv rator env)
                                  (box(val-of-cbv rand env)))])))


;----------------------------------------------------------------
; Call-by-reference Interpreter
; ---------------------------------------------------------------
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
      
      [(,rator ,rand) (guard (symbol? rand)) (apply-proc (val-of-cbr rator env)
                                  (apply-env env rand))]
      [(,rator ,rand) (apply-proc (val-of-cbr rator env)
                                  (box (val-of-cbr rand env)))])))


;----------------------------------------------------------------
; Call-by-name Interpreter
; ---------------------------------------------------------------
(define val-of-cbname
  (lambda (exp env)
    (pmatch exp
      [,b (guard (boolean? b)) b]
      [,n (guard (number? n)) n]
      [,x (guard (symbol? x)) ((unbox (apply-env env x)))]
      [(zero? ,n) (zero? (val-of-cbname n env))]
      [(sub1 ,n) (sub1 (val-of-cbname n env))]
      [(* ,n1 ,n2) (* (val-of-cbname n1 env) (val-of-cbname n2 env))]
      [(+ ,n1 ,n2) (+ (val-of-cbname n1 env) (val-of-cbname n2 env))]
      [(lambda (,x) ,body) (closure-cbname x body env)]
      [(if ,test ,conseq ,alt) (if (val-of-cbname test env)
                                   (val-of-cbname conseq env)
                                   (val-of-cbname alt env))]
      [(begin2 ,e1 ,e2) (begin (val-of-cbname e1 env) (val-of-cbname e2 env))]
      [(random ,n) (random n)]
      [(set! ,x ,rhs) (set-box! (apply-env env x) (lambda ()(val-of-cbname rhs env)))] 
      
      [(,rator ,rand) (guard (symbol? rand)) (apply-proc (val-of-cbname rator env)
                                  (apply-env env rand))]
      [(,rator ,rand) (apply-proc (val-of-cbname rator env)
                                  (box (lambda ()(val-of-cbname rand env))))])))


;----------------------------------------------------------------
; Call-by-need Interpreter
; ---------------------------------------------------------------
(define val-of-cbneed
  (lambda (exp env)
    (pmatch exp
      [,b (guard (boolean? b)) b]
      [,n (guard (number? n)) n]
      [,x (guard (symbol? x)) (unbox* (apply-env env x))]
      [(zero? ,n) (zero? (val-of-cbneed n env))]
      [(sub1 ,n) (sub1 (val-of-cbneed n env))]
      [(* ,n1 ,n2) (* (val-of-cbneed n1 env) (val-of-cbneed n2 env))]
      [(+ ,n1 ,n2) (+ (val-of-cbneed n1 env) (val-of-cbneed n2 env))]
      [(lambda (,x) ,body) (closure-cbneed x body env)]
      [(if ,test ,conseq ,alt) (if (val-of-cbneed test env)
                                   (val-of-cbneed conseq env)
                                   (val-of-cbneed alt env))]
      [(begin2 ,e1 ,e2) (begin (val-of-cbneed e1 env) (val-of-cbneed e2 env))]
      [(random ,n) (random n)]
      [(set! ,x ,rhs) (set-box! (apply-env env x) (lambda ()(val-of-cbneed rhs env)))] 
      
      [(,rator ,rand) (guard (symbol? rand)) (apply-proc (val-of-cbneed rator env)
                                  (apply-env env rand))]
      [(,rator ,rand) (apply-proc (val-of-cbneed rator env)
                                  (box (lambda () (val-of-cbneed rand env))))])))

;; The unbox* used for in the val-of-cbneed
(define unbox*
  (lambda (x-box)
    (let ([v ((unbox x-box))])
      (set-box! x-box (lambda () v))
      v)))


;----------------------------------------------------------------
; The usual suspects (helpers :))
; ---------------------------------------------------------------
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

;; Closure for the call-by-value 
(define closure-cbv
  (lambda (x body env)
    (lambda (a) (val-of-cbv body (extend-env env x a)))))

;; Closure for the call-by-reference
(define closure-cbr
  (lambda (x body env)
    (lambda (a) (val-of-cbr body (extend-env env x a)))))

;; Closure for the call-by-name
(define closure-cbname
  (lambda (x body env)
    (lambda (a) (val-of-cbname body (extend-env env x a)))))

;; Closure for the call-by-need
(define closure-cbneed
  (lambda (x body env)
    (lambda (a) (val-of-cbneed body (extend-env env x a)))))


;----------------------------------------------------------------
; Test cases for the four interpreters
; ---------------------------------------------------------------
(printf "\n=================================================\nTests cases for call-by-value Interpreter\n=================================================\n")

;; Making sure set! works
(test "set!"
  (val-of-cbv
   '((lambda (x) (begin2 (set! x #t)
                         (if x 3 5))) #f)
   (empty-env))
  3)

;; Returns 3 under CBV (compare with "interesting-cbr-1)
(test "interesting-cbv-1"
  (val-of-cbv
   '((lambda (a)
       ((lambda (p)
          (begin2
           (p a)
           a)) (lambda (x) (set! x 4)))) 3)
   (empty-env))
  3)

;; Returns 55 under CBV!  You can change the "begin2" to
;; "begin" and evaluate this in the Scheme REPL as evidence that
;; Scheme uses CBV.
;; (compare with "interesting-cbr-2)
(test "interesting-cbv-2"
  (val-of-cbv
   '((lambda (f)
       ((lambda (g)
          ((lambda (z) (begin2
                        (g z)
                        z))
           55))
        (lambda (y) (f y)))) (lambda (x) (set! x 44)))
   (empty-env))
  55)

;; Returns 33 under CBV (compare with "interesting-cbr-3)
(test "interesting-cbv-3"
  (val-of-cbv
   '((lambda (swap)
       ((lambda (a)
          ((lambda (b)
             (begin2
              ((swap a) b)
              a)) 44)) 33))
     (lambda (x)
       (lambda (y)
         ((lambda (temp)
            (begin2
             (set! x y)
             (set! y temp))) x))))
   (empty-env))
  33)


(printf "\n=================================================\nTests cases for call-by-reference Interpreter\n=================================================\n")

;; Making sure set! works
(test "set!"
  (val-of-cbr
   '((lambda (x) (begin2 (set! x #t)
                         (if x 3 5))) #f)
   (empty-env))
  3)

;; Swap variables with CBR
(test "swap-cbr"
    (val-of-cbr
     '((lambda (swap)
         ((lambda (a)
            ((lambda (b)
               (begin2 ((swap a) b)
                 (sub1 a))) 5))3))
       (lambda (x)
         (lambda (y)
           ((lambda (temp)
              (begin2 (set! temp y) (begin2 (set! y x) (set! x temp)))) #f))))
     (empty-env))  
    4)

;; Returns 4 under CBR (compare with "interesting-cbv-1")
(test "interesting-cbr-1"
  (val-of-cbr
   '((lambda (a)
       ((lambda (p)
          (begin2
           (p a)
           a)) (lambda (x) (set! x 4)))) 3)
   (empty-env))
  4)
 
 
;; returns 44 under CBR (compare with "interesting-cbv-2")
(test "interesting-cbr-2"
  (val-of-cbr
   '((lambda (f)
       ((lambda (g)
          ((lambda (z) (begin2
                        (g z)
                        z))
           55))
        (lambda (y) (f y)))) (lambda (x) (set! x 44)))
   (empty-env))
  44)
 
;; Returns 44 under CBR (compare with "interesting-cbv-3)
(test "interesting-cbr-3"
  (val-of-cbr
   '((lambda (swap)
       ((lambda (a)
          ((lambda (b)
             (begin2
              ((swap a) b)
              a)) 44)) 33))
     (lambda (x)
       (lambda (y)
         ((lambda (temp)
            (begin2
             (set! x y)
             (set! y temp))) x))))
   (empty-env))
  44)
 
 
(define random-sieve
  '((lambda (n)
      (if (zero? n)
          (if (zero? n) (if (zero? n) (if (zero? n) (if (zero? n) (if (zero? n) (if (zero? n) #t #f) #f) #f) #f) #f) #f)
          (if (zero? n) #f (if (zero? n) #f (if (zero? n) #f (if (zero? n) #f (if (zero? n) #f (if (zero? n) #f #t))))))))
    (random 2)))
 

(printf "\n=================================================\nTests cases for call-by-name Interpreter\n=================================================\n")
;; call-by-name
;;P(false positive) ≤ .01                                                     
(test "random-by-name"
  (val-of-cbname random-sieve (empty-env)) #f)

;; Does not terminate when tried with val-of-cbr, val-of-cbv
(test "omega-by-name"
  (val-of-cbname
   '((lambda (z) 100)
     ((lambda (x) (x x)) (lambda (x) (x x))))
   (empty-env))
  100)
 

(printf "\n=================================================\nTests cases for call-by-need Interpreter\n=================================================\n")
;; call-by-need                                                                  
(test "random-by-need"
  (val-of-cbneed random-sieve (empty-env)) #t)
 
;; Does not terminate when tried with val-of-cbr, val-of-cbv
(test "omega-by-need"
  (val-of-cbname
   '((lambda (z) 100)
     ((lambda (x) (x x)) (lambda (x) (x x))))
   (empty-env))
  100)


;==============================================Optional================================================
;------------------------------------------------------------------------------------------------------
;Function Definitions
;------------------------------------------------------------------------------------------------------
;;(define base
;;  (lambda (t)
;;    `(0 . ,t)))

;;(define grow
;;  (lambda (f)
;;    (lambda (c)
;;      (let ((c^ (f (cdr c))))
;;        (cons (+ (car c) (car c^)) (cdr c^))))))

;;(define o
;;  (lambda (f)
;;    (lambda (g)
;;      (lambda (x)
;;        (f (g x))))))


;==============================================Proof1==================================================
;------------------------------------------------------------------------------------------------------
;(grow base) = (lambda (c) c)
;------------------------------------------------------------------------------------------------------
;Step1: Beta substitute base into grow, i.e. (grow base)

;;(lambda (c)
;;  (let ((c^ ((lambda (t)
;;               `(0 . ,t)) (cdr c))))
;;    (cons (+ (car c) (car c^)) (cdr c^))))
;------------------------------------------------------------------------------------------------------
;Step2: Beta substitute (cdr c) into t

;;(lambda (c)
;;  (let ((c^ `(0 . ,(cdr c))))
;;    (cons (+ (car c) (car c^)) (cdr c^))))
;------------------------------------------------------------------------------------------------------
;Step3: Using (let ([x y]) body) = ((lambda (x) body) y)

;;(lambda (c)
;;  ((lambda (c^)
;;    (cons (+ (car c) (car c^)) (cdr c^))) `(0 . ,(cdr c))))
;------------------------------------------------------------------------------------------------------
;Step4: Beta substitute `(0 . ,(cdr c)) into c^

;;(lambda (c)
;;  (cons (+ (car c) (car `(0 . ,(cdr c)))) (cdr `(0 . ,(cdr c)))))
;------------------------------------------------------------------------------------------------------
;Step5: Evaluate (car `(0 . ,(cdr c))) and (cdr `(0 . ,(cdr c)))

;;(lambda (c)
;;  (cons (+ (car c) 0) (cdr c)))
;------------------------------------------------------------------------------------------------------
;Step6: Evaluate (+ (car c) 0)

;;(lambda (c)
;;  (cons (car c) (cdr c)))
;------------------------------------------------------------------------------------------------------
;Step7: Evaluate (cons (car c) (cdr c))

;;(lambda (c)
;;  c)
;------------------------------------------------------------------------------------------------------
;Therefore, we now have our result,
;
;(grow base) = (lambda (c) c)
;==========================================End of Proof1===============================================


;==============================================Proof2==================================================
;------------------------------------------------------------------------------------------------------
;((o (grow f)) base) = f
;------------------------------------------------------------------------------------------------------
;Step1: Beta substitute f into grow, i.e. (grow f)

;;(lambda (c)
;;  (let ((c^ (f (cdr c))))
;;    (cons (+ (car c) (car c^)) (cdr c^))))
;------------------------------------------------------------------------------------------------------
;Step2: Beta substitute (grow f) into o, i.e. (o (grow f))

;;(lambda (g)
;;  (lambda (x)
;;    ((lambda (c)
;;       (let ((c^ (f (cdr c))))
;;         (cons (+ (car c) (car c^)) (cdr c^)))) (g x))))
;------------------------------------------------------------------------------------------------------
;Step3: Beta substitute base into (o (grow f)), i.e. ((o (grow f)) base)

;;(lambda (x)
;;  ((lambda (c)
;;     (let ((c^ (f (cdr c))))
;;       (cons (+ (car c) (car c^)) (cdr c^)))) ((lambda (t)
;;                                                 `(0 . ,t)) x)))
;------------------------------------------------------------------------------------------------------
;Step4: Beta substitute x into t

;;(lambda (x)
;;  ((lambda (c)
;;     (let ((c^ (f (cdr c))))
;;       (cons (+ (car c) (car c^)) (cdr c^)))) `(0 . ,x)))
;------------------------------------------------------------------------------------------------------
;Step5: Beta substitute `(0 . ,x) into c

;;(lambda (x)
;;  (let ((c^ (f (cdr `(0 . ,x)))))
;;    (cons (+ (car `(0 . ,x)) (car c^)) (cdr c^))))
;------------------------------------------------------------------------------------------------------
;Step6: Using (let ([x y]) body) = ((lambda (x) body) y)

;;(lambda (x)
;;  ((lambda (c^)
;;     (cons (+ (car `(0 . ,x)) (car c^)) (cdr c^))) (f (cdr `(0 . ,x)))))
;------------------------------------------------------------------------------------------------------
;Step7: Beta substitute (f (cdr `(0 . ,x))) into c^

;;(lambda (x)
;;  (cons (+ (car `(0 . ,x)) (car (f (cdr `(0 . ,x))))) (cdr (f (cdr `(0 . ,x))))))
;------------------------------------------------------------------------------------------------------
;Step8: Evalute car and cdr expressions for (f (cdr `(0 . ,x)))

;;(lambda (x)
;;  (cons (+ (car `(0 . ,x)) (car (f x))) (cdr (f x))))
;------------------------------------------------------------------------------------------------------
;Step9: Eevaluate car of `(0 . ,x)

;;(lambda (x)
;;  (cons (+ 0 (car (f x))) (cdr (f x))))
;------------------------------------------------------------------------------------------------------
;Step10: Evaluate +

;;(lambda (x)
;;  (cons (car (f x)) (cdr (f x))))
;------------------------------------------------------------------------------------------------------
;The result we have from the last step refers to a function 'f' which is in fact the
;function referred to by the body of 'grow'. This is ultimately the external function we
;gave to 'grow', i.e. the 'f' in here is actually the 'f' in '((o (grow f)) base)'.
;
;The 'grow' function expects a function (referred to as 'f' in its body) as its argument. 
;The 'f' should be a function which takes a single input and returns a pair according to 
;the definition of 'grow'. 
;
;The above two pragraphs explain that the expression '(f x)' in the last step actually
;returns a pair which is equal to the pair returned by applying the original function
;'f' to 'x'
;
;Taking the car and cdr of a pair and cons them together results an equal pair to the orignal.
;Therefore, the pair returned by '(cons (car (f x)) (cdr (f x)))' is equal to the pair returned 
;by '(f x)' in the last step.

;Therefore we can simplify the last step further into

;;(lambda (x)
;;  (f x))

;This is simply an equivalent function to 'f'. Therefore, we get the final answer
;
;((o (grow f)) base) = f
;==========================================End of Proof2===============================================


;==============================================Proof3==================================================
;------------------------------------------------------------------------------------------------------
;(grow ((o (grow f)) g)) = ((o (grow f)) (grow g))
;------------------------------------------------------------------------------------------------------
;Step1: Take the result of (o (grow f)) from Proof2

;;(lambda (g)
;;  (lambda (x)
;;    ((lambda (c)
;;       (let ((c^ (f (cdr c))))
;;         (cons (+ (car c) (car c^)) (cdr c^)))) (g x))))
;------------------------------------------------------------------------------------------------------
;Step2: Beta substitute (g x) into c

;;(lambda (g)
;;  (lambda (x)
;;    (let ((c^ (f (cdr (g x)))))
;;      (cons (+ (car (g x)) (car c^)) (cdr c^)))))
;------------------------------------------------------------------------------------------------------
;Step3: Using (let ([x y]) body) = ((lambda (x) body) y)

;;(lambda (g)
;;  (lambda (x)
;;    ((lambda (c^)
;;       (cons (+ (car (g x)) (car c^)) (cdr c^)))
;;     (f (cdr (g x))))))
;------------------------------------------------------------------------------------------------------
;Step4: Beta substitute (f (cdr (g x))) into c^. This is still (o (grow f))
;       Let's call this P

;;(lambda (g)
;;  (lambda (x)
;;    (cons (+ (car (g x)) (car (f (cdr (g x))))) (cdr (f (cdr (g x)))))))
;------------------------------------------------------------------------------------------------------
;Step5: Beta substitute g into the above step, i.e. ((o (grow f)) g)

;;(lambda (x)
;;  (cons (+ (car (g x)) (car (f (cdr (g x))))) (cdr (f (cdr (g x))))))
;------------------------------------------------------------------------------------------------------
;Step6: Beta substitute the last result into grow, i.e. (grow ((o (grow f)) g))

;;(lambda (c)
;;  (let ((c^ ((lambda (x)
;;               (cons (+ (car (g x)) (car (f (cdr (g x))))) (cdr (f (cdr (g x)))))) (cdr c))))
;;    (cons (+ (car c) (car c^)) (cdr c^))))
;------------------------------------------------------------------------------------------------------
;Step7: Beta substitute (cdr c) into x

;;(lambda (c)
;;  (let ((c^ (cons (+ (car (g (cdr c))) (car (f (cdr (g (cdr c)))))) (cdr (f (cdr (g (cdr c))))))))
;;    (cons (+ (car c) (car c^)) (cdr c^))))
;------------------------------------------------------------------------------------------------------
;Step8: Evaluating (car c^) and (cdr c^) and using (let ([x y]) body) = ((lambda (x) body) y)
;       Let's call this Q

;;(lambda (c)
;;  (cons (+ (car c) (+ (car (g (cdr c))) (car (f (cdr (g (cdr c))))))) (cdr (f (cdr (g (cdr c)))))))
;------------------------------------------------------------------------------------------------------
;Step9: Now let's figure out what RHS is all about.
;       Take the reduced version of (o (grow f)), i.e. P

;;(lambda (g)
;;  (lambda (x)
;;    (cons (+ (car (g x)) (car (f (cdr (g x))))) (cdr (f (cdr (g x)))))))
;------------------------------------------------------------------------------------------------------
;Step10: Beta substitute g into grow, i.e. (grow g)

;;(lambda (c)
;;  (let ((c^ (g (cdr c))))
;;    (cons (+ (car c) (car c^)) (cdr c^))))
;------------------------------------------------------------------------------------------------------
;Step11: Using (let ([x y]) body) = ((lambda (x) body) y) and beta substituion of (g (cdr c)) into c^.
;        This is still (grow g)

;;(lambda (c)
;;  (cons (+ (car c) (car (g (cdr c)))) (cdr (g (cdr c)))))
;------------------------------------------------------------------------------------------------------
;Step12: Beta substitute (grow g) into (o (grow f)), i.e. ((o (grow f)) (grow g))

;;(lambda (x)
;;  (cons (+ (car ((lambda (c)
;;                   (cons (+ (car c) (car (g (cdr c)))) (cdr (g (cdr c))))) x)) (car (f (cdr ((lambda (c)
;;                                                                                               (cons (+ (car c) (car (g (cdr c)))) (cdr (g (cdr c))))) x))))) (cdr (f (cdr ((lambda (c)
;;                                                                                                                                                                              (cons (+ (car c) (car (g (cdr c)))) (cdr (g (cdr c))))) x))))))
;------------------------------------------------------------------------------------------------------
;Step13: Beta substitution of x into c

;;(lambda (x)
;;  (cons (+ (car (cons (+ (car x) (car (g (cdr x)))) (cdr (g (cdr x))))) (car (f (cdr (cons (+ (car x) (car (g (cdr x)))) (cdr (g (cdr x)))))))) (cdr (f (cdr (cons (+ (car x) (car (g (cdr x)))) (cdr (g (cdr x)))))))))
;------------------------------------------------------------------------------------------------------
;Step14: Evaluate possible car and cdr
;        Let's call this R

;;(lambda (x)
;;  (cons (+ (+ (car x) (car (g (cdr x)))) (car (f (cdr (g (cdr x)))))) (cdr (f (cdr (g (cdr x)))))))
;------------------------------------------------------------------------------------------------------
;Step15: Now let's look at Q again, which is the reduced version of the LHS

;;(lambda (c)
;;  (cons (+ (car c) (+ (car (g (cdr c))) (car (f (cdr (g (cdr c))))))) (cdr (f (cdr (g (cdr c)))))))
;------------------------------------------------------------------------------------------------------
;Step16: Alpha substitute x into c

;;(lambda (x)
;;  (cons (+ (car x) (+ (car (g (cdr x))) (car (f (cdr (g (cdr x))))))) (cdr (f (cdr (g (cdr x)))))))
;------------------------------------------------------------------------------------------------------
;Step17: The addition is associative. Therefore, we can alter the grouping of addition in the above step to
;        form the following, let's say L

;;(lambda (x)
;;  (cons (+ (+ (car x) (car (g (cdr x)))) (car (f (cdr (g (cdr x)))))) (cdr (f (cdr (g (cdr x)))))))
;------------------------------------------------------------------------------------------------------
;Now we see that L, which is the re-ordered reduced version of LHS is equal to the reduced version of
;RHS, R.
;
;Therefore, we get our final answer,
;
;(grow ((o (grow f)) g)) = ((o (grow f)) (grow g))
;==========================================End of Proof3===============================================
