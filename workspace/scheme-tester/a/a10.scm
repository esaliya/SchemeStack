;;----------------------------------
;; B521 - Assignment 10
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


;--------------------------------------------------------------------------------------
; Store Monad Definition
;--------------------------------------------------------------------------------------
(define unit_store
  (lambda (a)
    (lambda (s)     ;; <-------------------- this lambda is a Ma                
      `(,a . ,s))))
 
(define star_store
  (lambda (f)
    (lambda (Ma)
      (lambda (s)   ;; <-------------------- this lambda is a Ma                
        (let ((p (Ma s)))
          (let ((new-a (car p)) (new-s (cdr p)))
            (let ((new-Ma (f new-a)))
              (new-Ma new-s))))))))


;--------------------------------------------------------------------------------------
; Given definition of rember*evenXhowmanyeven
;--------------------------------------------------------------------------------------
;;(define rember*evenXhowmanyeven
;;  (lambda (l)
;;    (cond
;;      ((null? l) (unit_store '()))
;;      ((pair? (car l))
;;       ((star_store
;;         (lambda (a)
;;           ((star_store (lambda (d) (unit_store (cons a d))))
;;            (rember*evenXhowmanyeven (cdr l)))))
;;        (rember*evenXhowmanyeven (car l))))
;;      ((odd? (car l))
;;       ((star_store (lambda (d) (unit_store (cons (car l) d))))
;;        (rember*evenXhowmanyeven (cdr l))))
;;      (else
;;       ((star_store (lambda (__) (rember*evenXhowmanyeven (cdr l))))
;;        (lambda (s) `(__ . ,(add1 s))))))))


;--------------------------------------------------------------------------------------
; rember*evenXhowmanyeven
;--------------------------------------------------------------------------------------
(define rember*evenXhowmanyeven
  (lambda (l)
    (cond
      ((null? l) (unit_store '()))
      ((pair? (car l))
       ((star_store
         (lambda (a)
           ((star_store (lambda (d) (unit_store (cons a d))))
            (rember*evenXhowmanyeven (cdr l)))))
        (rember*evenXhowmanyeven (car l))))
      ((odd? (car l))
       ((star_store (lambda (d) (unit_store (cons (car l) d))))
        (rember*evenXhowmanyeven (cdr l))))
      (else
       ((star_store (lambda (__) (rember*evenXhowmanyeven (cdr l))))
        (lambda (s) `(__ . ,(add1 s))))))))


;--------------------------------------------------------------------------------------
; rember*noneXhowmanyeven
;--------------------------------------------------------------------------------------
(define rember*noneXhowmanyeven
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*noneXhowmanyeven (car l))) ))
                        (rember*noneXhowmanyeven (cdr l)))]
      [(odd? (car l)) ((star_store (lambda (d) (unit_store (cons (car l) d))))
                       (rember*noneXhowmanyeven (cdr l)))]        
                                  
      [else ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons d a))))
                                      (rember*noneXhowmanyeven (cdr l)))))
             (lambda (s) `(,(car l) . ,(add1 s))))])))


;--------------------------------------------------------------------------------------
; rember*evenXhowmanyodd
;--------------------------------------------------------------------------------------
(define rember*evenXhowmanyodd
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*evenXhowmanyodd (car l))) ))
                        (rember*evenXhowmanyodd (cdr l)))]
      
      [(odd? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons d a))))
                                                (rember*evenXhowmanyodd (cdr l)))))
                       (lambda (s) `(,(car l) . ,(add1 s))))]      
      
                                  
      [else ((star_store (lambda (d) (unit_store d)))
             (rember*evenXhowmanyodd (cdr l)))])))


;--------------------------------------------------------------------------------------
; rember*oddXhowmanyeven
;--------------------------------------------------------------------------------------
; We could either change odd? to even? as in here or swap the RHS of odd? with else
(define rember*oddXhowmanyeven
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*oddXhowmanyeven (car l))) ))
                        (rember*oddXhowmanyeven (cdr l)))]
      
      [(even? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons d a))))
                                                (rember*oddXhowmanyeven (cdr l)))))
                       (lambda (s) `(,(car l) . ,(add1 s))))]      
      
                                  
      [else ((star_store (lambda (d) (unit_store d)))
             (rember*oddXhowmanyeven (cdr l)))])))


;--------------------------------------------------------------------------------------
; rember*evenXsumofeven
;--------------------------------------------------------------------------------------
(define rember*evenXsumofeven
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*evenXsumofeven (car l))) ))
                        (rember*evenXsumofeven (cdr l)))]
      
      [(even? (car l)) ((star_store (lambda (__) (rember*evenXsumofeven (cdr l))))
                        (lambda (s) `(__ . ,(+ (car l) s))))]
      
                                  
      [else ((star_store (lambda (d) (unit_store (cons (car l) d))))
             (rember*evenXsumofeven (cdr l)))])))


;--------------------------------------------------------------------------------------
; rember*evenXdifferenceofoddsandevens
;--------------------------------------------------------------------------------------
(define rember*evenXdifferenceofoddsandevens
  (lambda (l)
    (cond
      [(null? l) (unit_store l)]
      [(pair? (car l)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                                 (rember*evenXdifferenceofoddsandevens (car l))) ))
                        (rember*evenXdifferenceofoddsandevens (cdr l)))]
      
      [(even? (car l)) ((star_store (lambda (__) (rember*evenXdifferenceofoddsandevens (cdr l))))
                        (lambda (s) `(__ . ,(- s (car l)))))]
      
                                  
      [else ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons d a))))
                                      (rember*evenXdifferenceofoddsandevens (cdr l)))))
             (lambda (s) `(,(car l) . ,(+ s (car l)))))])))


;--------------------------------------------------------------------------------------
; zeroXfact
;--------------------------------------------------------------------------------------
(define zeroXfact
  (lambda (n)
    (cond 
      [(zero? n) (unit_store 0)]
      [else ((star_store (lambda (__) (zeroXfact (sub1 n))))
             (lambda (s) `(__ . ,(* s n))))])))


;--------------------------------------------------------------------------------------
; binaryXdecimal
;--------------------------------------------------------------------------------------
(define binaryXdecimal
  (lambda (l)
    (cond
      [(null? l) ((star_store (lambda (__) (unit_store '())))
                  (lambda (s)
                    `(__ . 0)))]
                              
      [else ((star_store (lambda (a) ((star_store (lambda (d) ((star_store (lambda (__) (unit_store (cons (car l) d))))
                                                                (lambda (s)
                                                                  (cond
                                                                    [(eq? 1 (car l)) `(__ . ,(+ s a))]
                                                                    [else `(__ . ,s)])))))
                                       (binaryXdecimal (cdr l)))))
              (lambda (s)
                (cond
                  [(eq? 0 s) `(1 . 1)]
                  [else `(,(* 2 s) . ,(* 2 s))])))])))


;--------------------------------------------------------------------------------------
; Direct style definition of power
;--------------------------------------------------------------------------------------
;;(define power
;;  (lambda (x n)
;;    (cond
;;      [(zero? n) 1]
;;      [(= n 1) x]
;;      [(odd? n) (* x (power x (sub1 n)))]
;;      [(even? n) (let ((nhalf (/ n 2)))
;;                   (let ((y (power x nhalf)))
;;                     (* y y)))])))

;--------------------------------------------------------------------------------------
; powerXhowmanymults
;--------------------------------------------------------------------------------------
(define powerXhowmanymults
  (lambda (x n)
    (cond
      [(zero? n) (unit_store 1)]
      [(= n 1) (unit_store x)]
      [(odd? n) ((star_store (lambda (__) ((star_store (lambda (d) (unit_store (* x d))))
                                           (powerXhowmanymults x (sub1 n)))))
                 (lambda (s)
                   `(__ . ,(add1 s))))]
      [(even? n) ((star_store (lambda (__) ((star_store (lambda (d) (unit_store (* d d))))
                                            (powerXhowmanymults x (/ n 2)))))
                  (lambda (s)
                    `(__ . ,(add1 s))))])))


;--------------------------------------------------------------------------------------
; howmanymultsXpower
;--------------------------------------------------------------------------------------
(define howmanymultsXpower
  (lambda (x n)
    (cond
      [(zero? n) ((star_store (lambda (d) (unit_store d)))
                  (lambda (s) 
                    `(0 . 1)))]
      [(= n 1) ((star_store (lambda (d) (unit_store d)))
                  (lambda (s) 
                    `(0 . ,x)))]
      [(odd? n) ((star_store (lambda (d)
                               ((star_store (lambda (__) (unit_store (+ d 1))))
                                (lambda (s)
                                  `(__ . ,(* x s))))))
                 (howmanymultsXpower x (sub1 n)))]
      
      [(even? n) ((star_store (lambda (d)
                                ((star_store (lambda (__) (unit_store (+ d 1))))
                                 (lambda (s)
                                   `(__ . ,(* s s))))))
                  (howmanymultsXpower x (/ n 2)))])))


;--------------------------------------------------------------------------------------
; Test cases for the monadic style functions
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for the Monadic style functions\n=================================================\n")

(test "rember*noneXhowmanyeven-a"
  ((rember*noneXhowmanyeven '(2 3 (7 4 5 6) 8 (9) 2)) 0)
  '((2 3 (7 4 5 6) 8 (9) 2) . 5))

(test "rember*noneXhowmanyeven-b"
  ((rember*noneXhowmanyeven '()) 0)
  '(() . 0))

(test "rember*noneXhowmanyeven-c"
  ((rember*noneXhowmanyeven '((1) ((2) 3) 5)) 0)
  '(((1) ((2) 3) 5) . 1))

(printf "\n")

(test "rember*evenXhowmanyodd-a"
  ((rember*evenXhowmanyodd '(2 3 (7 4 5 6) 8 (9) 2)) 0)
  '((3 (7 5) (9)) . 4))

(test "rember*evenXhowmanyodd-b"
  ((rember*evenXhowmanyodd '()) 0)
  '(() . 0))

(test "rember*evenXhowmanyodd-c"
  ((rember*evenXhowmanyodd '((1) ((2) 3) 5)) 0)
  '(((1) (() 3) 5) . 3))

(printf "\n")

(test "rember*oddXhowmanyeven-a"
  ((rember*oddXhowmanyeven '(2 3 (7 4 5 6) 8 (9) 2)) 0)
  '((2 (4 6) 8 () 2) . 5))

(test "rember*oddXhowmanyeven-b"
  ((rember*oddXhowmanyeven '()) 0)
  '(() . 0))

(test "rember*oddXhowmanyeven-c"
  ((rember*oddXhowmanyeven '((1) ((2) 3) 5)) 0)
  '((() ((2))) . 1))

(printf "\n")

(test "rember*evenXsumofeven-a"
  ((rember*evenXsumofeven '(2 3 (7 4 5 6) 8 (9) 2)) 0)
  '((3 (7 5) (9)) . 22))

(test "rember*evenXsumofeven-b"
  ((rember*evenXsumofeven '()) 0)
  '(() . 0))

(test "rember*evenXsumofeven-c"
  ((rember*evenXsumofeven '((1) ((2) 3) 5)) 0)
  '(((1) (() 3) 5) . 2))

(printf "\n")

(test "rember*evenXdifferenceofoddsandevens-a"
  ((rember*evenXdifferenceofoddsandevens '(2 3 (7 4 5 6) 8 (9) 2)) 0)
  '((3 (7 5) (9)) . 2))

(test "rember*evenXdifferenceofoddsandevens-b"
  ((rember*evenXdifferenceofoddsandevens '(2 3 (7 4 5 6) 8 (9) 2 20)) 0)
  '((3 (7 5) (9)) . -18))

(test "rember*evenXdifferenceofoddsandevens-c"
  ((rember*evenXdifferenceofoddsandevens '()) 0)
  '(() . 0))

(test "rember*evenXdifferenceofoddsandevens-d"
  ((rember*evenXdifferenceofoddsandevens '((1) ((2) 3) 5)) 0)
  '(((1) (() 3) 5) . 7))

(printf "\n")

(test "zeroXfact-a"
  ((zeroXfact 0) 1)
  '(0 . 1))

(test "zeroXfact-b"
  ((zeroXfact 1) 1)
  '(0 . 1))

(test "zeroXfact-c"
  ((zeroXfact 5) 1)
  '(0 . 120))

(printf "\n")

(test "binaryXdecimal-a"
  ((binaryXdecimal '(0)) 0)
  '((0) . 0))

(test "binaryXdecimal-b"
  ((binaryXdecimal '(0 0 1)) 0)
  '((0 0 1) . 4))

(test "binaryXdecimal-c"
  ((binaryXdecimal '(0 0 1 1)) 0)
  '((0 0 1 1) . 12))

(test "binaryXdecimal-d"
  ((binaryXdecimal '(1 1 1 1)) 0)
  '((1 1 1 1) . 15))

(test "binaryXdecimal-e"
  ((binaryXdecimal '(1 0 1 0 1)) 0)
  '((1 0 1 0 1) . 21))

(test "binaryXdecimal-f"
  ((binaryXdecimal '(1 1 1 1 1 1 1 1 1 1 1 1 1)) 0)
  '((1 1 1 1 1 1 1 1 1 1 1 1 1) . 8191))

(printf "\n")

(test "powerXhowmanymults-a"
  ((powerXhowmanymults 2 0) 0)
  '(1 . 0))

(test "powerXhowmanymults-b"
  ((powerXhowmanymults 2 2) 0)
  '(4 . 1))

(test "powerXhowmanymults-c"
  ((powerXhowmanymults 2 10) 0)
  '(1024 . 4))

(test "powerXhowmanymults-d"
  ((powerXhowmanymults 10 5) 0)
  '(100000 . 3))

(test "powerXhowmanymults-e"
  ((powerXhowmanymults 3 31) 0)
  '(617673396283947 . 8))

(test "powerXhowmanymults-f"
  ((powerXhowmanymults 3 32) 0)
  '(1853020188851841 . 5))

(printf "\n")

(test "howmanymultsXpower-a"
  ((howmanymultsXpower 2 0) 2)
  '(0 . 1))

(test "howmanymultsXpower-a"
  ((howmanymultsXpower 2 2) 2)
  '(1 . 4))

(test "howmanymultsXpower-a"
  ((howmanymultsXpower 2 10) 2)
  '(4 . 1024))

(test "howmanymultsXpower-a"
  ((howmanymultsXpower 10 5) 10)
  '(3 . 100000))

(test "howmanymultsXpower-a"
  ((howmanymultsXpower 3 31) 3)
  '(8 . 617673396283947))

(test "howmanymultsXpower-a"
  ((howmanymultsXpower 3 32) 3)
  '(5 . 1853020188851841))


;--------------------------------------------------------------------------------------
; Brainteaser - Part1
;--------------------------------------------------------------------------------------
(define unitcps
  (lambda (a)
    (lambda (k) ; ⇐= This lambda is a Ma.
      (k a))))

(define starcps
  (lambda (f)
    (lambda (Ma)
      (lambda (k) ; ⇐= This lambda is a Ma.                 
        (let ((k^ (lambda (a)
                    (let ((Ma^ (f a)))
                      (Ma^ k )))))
          (Ma k^))))))

(define callcc
  (lambda (g)
    (lambda (k)
      (let ((k-as-proc (lambda (a) (lambda (k_ignored) (k a)))))
        (let ((Ma (g k-as-proc)))
          (Ma k))))))


(define value-of-cps
  (lambda (expr env)
    (pmatch expr
      [,n (guard (or (number? n) (boolean? n))) (unitcps n)]      
      [,x (guard (symbol? x)) (apply-env-cps env x)]
      [(* ,x1 ,x2) ((starcps (lambda (v) ((starcps (lambda (w) (unitcps (* v w))))
                                         (value-of-cps x2 env))))
                    (value-of-cps x1 env))]       
      [(sub1 ,x) ((starcps (lambda (v) (unitcps (sub1 v))))
                  (value-of-cps x env))]       
      [(zero? ,x) ((starcps (lambda (v) (unitcps (zero? v))))
                   (value-of-cps x env))]       
      [(if ,test ,conseq ,alt) ((starcps (lambda (b) (if b
                                                       (value-of-cps conseq env)
                                                       (value-of-cps alt env))))
                                (value-of-cps test env))]

      [(letcc ,k-id ,body) (callcc (lambda (out) 
                                      (value-of-cps body (extend-env k-id out env))))]

      [(throw ,v-exp ,k-exp) ((starcps (lambda (c) ((starcps (lambda (v) (c v)))
                                                    (value-of-cps v-exp env))))
                              (value-of-cps k-exp env))]       

      [(lambda (,id) ,body) (unitcps (closure id body env))]
      [(,rator ,rand) ((starcps (lambda (v) ((starcps (lambda (w) (apply-proc-cps w v)))
                                             (value-of-cps rator env))))
                       (value-of-cps rand env))])))
       

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
; Monadifed using CPS Monad: observers for environments and procedures based on data-structural 
; representation
;--------------------------------------------------------------------------------------
(define apply-env-cps
 (lambda (env y)
   (pmatch env
     [(mt-env) (error 'empty env "unbound variable ~s : discarding continuation" y)] ;let's keep it for the moment
     [(ext-env ,x ,a ,env) (if (eq? x y) (unitcps a) (apply-env-cps env y))])))

(define apply-proc-cps
  (lambda (p a)
    (pmatch p
      [(clos ,id ,body ,env) (value-of-cps body (extend-env id a env))])))


;--------------------------------------------------------------------------------------
; Test cases for Brainteaser - Part1, i.e. value-of-cps
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for the value-of-cps\n=================================================\n")
(define fact-5
  '((lambda (f)
      ((f f) 5))
    (lambda (f)
      (lambda (n)
	(if (zero? n)
            1
            (* n ((f f) (sub1 n))))))))
 
(test "fact-5"
  ((value-of-cps fact-5 (empty-env)) (lambda (v) v))
  120)
 
 
(define letcc-fun
  '(* 3 (letcc q (* 2 (throw 4 q)))))
 
(test "letcc"
  ((value-of-cps letcc-fun (empty-env)) (lambda (v) v))
  12)


