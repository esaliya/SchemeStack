;; --------------------------------------------------------------------------
;; Abstract machine corresponding to the CAM (Categorical Abstract Machine)
;; -------------------------------------------------------------------------- 
;;
;; Reference:
;;   
;;   A Functional Correspondence between Evaluators and Abstract Machines
;;   Mads Sig Ager, et. al.
;;   BRICS, March 2003
;;   http://www.brics.dk/RS/04/3/BRICS-RS-04-3.pdf
;; 
;; Source syntax:
;;  
;;   t ::= n | λt | t0 t1 | nil | (cons t1 t2) | (car t) | (cdr t)
;;
;;   Note. In the implementation we assume the following change to the
;;   source syntax
;;
;;            λt = (lambda t)
;;         t0 t1 = (t0 t1)
;; 
;; Expressible values (unit value, pairs, and closures) and evaluation
;; contexts
;;  
;;   v ::= null | (v1, v2) | [v, t]
;;   k ::= CONT0 | CONT1(t, k) | CONT2(k) | CONT3(t, k) 
;;         | CONT4(k) | CONT5(k) | CONT6(k)
;; 
;;   Note. In the implementation we represent these as datastructures
;; 
;;
;; Initial transition, transition rules (two kinds), and final transition:
;; 
;; --------------------------------------------------------------
;;                        t   =>   <t, null, nil, CONT0>
;; --------------------------------------------------------------
;;             <n, v, s, k>   =>   <k, γ(n, v), s>
;;            <λt, v, s, k>   =>   <k, [v,t], s>
;;           <nil, v, s, k>   =>   <k, null, s>
;;         <t0 t1, v, s, k>   =>   <t0, v, v::s, CONT1(t1,k)>
;;  <(cons t1 t2), v, s, k>   =>   <t1, v, v::s, CONT3(t2, k)>
;;       <(car t), v, s, k>   =>   <t, v, s, CONT5(k)>
;;       <(cdr t), v, s, k>   =>   <t, v, s, CONT6(k)>
;; --------------------------------------------------------------
;;  <CONT1(t, k), v, v'::s>   =>   <t, v', v::s, CONT2(k)>
;; <CONT2(k), v', [v,t]::s>   =>   <t, (v,v'), s, k>
;; <CONT3(t1, k), v, v'::s>   =>   <t1, v', v::s, CONT4(k)>
;;     <CONT4(k), v, v'::s>   =>   <k, (v',v),s>
;;  <CONT5(k), (v1, v2), s>   =>   <k, v1, s>
;;  <CONT6(k), (v1, v2), s>   =>   <k, v2, s>
;; --------------------------------------------------------------
;;         <CONT0, v, nil>    =>   v
;; --------------------------------------------------------------
;; 
;;  where,
;;     
;;   γ(0, (v1, v2)) = v2
;;   γ(n, (v1, v2)) = γ(n-1, v1)
;; 
;; --------------------------------------------------------------------------

;; --------------------------------------------------------------------------
;; Helpers
;; --------------------------------------------------------------------------

;; make context
(define make-cont
  (case-lambda
    [(n) `(cont ,n)]
    [(n k) `(cont ,n (,k))]
    [(n t k) `(cont ,n (,t ,k))]))

;; predicate for contexts
(define iscont?
  (lambda (k)
    (match k
      [(cont ,s* ...) #t]
      [,x #f])))

;; make closure
(define make-clos
  (lambda (v t)
    `(clos ,v ,t)))

;; predicate for closures
(define isclos?
  (lambda (c)
    (match c
      [(clos ,v ,t) #t]
      [,x #f])))

;; expressible value of a closure
(define closv
  (lambda (c)
    (match c
      [(clos ,v ,t) v]
      [,x (error 'closv (format "~s is not a closure" x))])))

;; term of a closure
(define clost
  (lambda (c)
    (match c
      [(clos ,v ,t) t]
      [,x (error 'closv (format "~s is not a closure" x))])))

;; make pair
(define make-pair
  (lambda (v1 v2)
    `(pair ,v1 ,v2)))

;; predicate for closures
(define ispair?
  (lambda (p)
    (match p
      [(pair ,v1 ,v2) #t]
      [,x #f])))

;; fst of a pair
(define fst
  (lambda (p)
    (match p
      [(pair ,v1 ,v2) v1]
      [,x (error 'fst (format "~s is not a pair" x))])))

;; snd of a pair
(define snd
  (lambda (p)
    (match p
      [(pair ,v1 ,v2) v2]
      [,x (error 'fst (format "~s is not a pair" x))])))

;; make null
(define make-null
  (lambda ()
    'null))

;; predicate for null
(define isnull?
  (lambda (n)
    (eq? 'null n)))

;; gamma
(define gamma
  (lambda (n v)
    (match v
      [(pair ,v1 ,v2) (if (zero? n) v2 (gamma (sub1 n) v1))]
      [,x (error 'gamma (format "~s is not a pair" x))])))

;; predicate for expressible values
(define isexpv?
  (lambda (v)
    (or (isnull? v) (ispair? v) (isclos? v))))


;; Store Implementation

;; Procedure to create a general store. The type? parameter defines 
;; the object type that can be store in the store. strategy defines
;; the in/out mechanism of the store. Possible values for this
;; parameter are 'stack and 'queue. First two will
;; essentially create a stack and a queue with LIFO and FIFO strategies.
;; 
;; Parameters
;;   - type?:    Predicate to test the type of objects 
;;   - strategy: Specifies the store in/out strategy. 
;;               Legal values for this are 'stack, and 'queue
(define make-store
  (lambda (type? strategy)
    (let ([s '()])
      (lambda fmls
        (case (car fmls)
          [(in!) (if (type? (cadr fmls))
                     (case strategy
                       [(stack) (set! s (cons (cadr fmls) s))]
                       [(queue) (set! s (append s (list (cadr fmls))))])
                     (error 'in! "invalid object type"))]
          [(out!) (if (null? s)
                      (error 'out! "empty store")
                      (let ([obj (car s)])
                            (set! s (cdr s))
                            obj))]          
          [(empty?) (null? s)]
          [(size) (length s)])))))
;; --------------------------------------------------------------------------


;; --------------------------------------------------------------------------
;; CAM
;; --------------------------------------------------------------------------
        
(define cam
  (lambda (t)
    (define cam-eval
      (trace-lambda valof (t v s k)
        (match t
          [(lambda ,t) (cam-cont k (make-clos v t) s)]
          [nil (cam-cont k (make-null) s)]
          [(cons ,t1 ,t2)
           (cam-eval t1 v (cons v s) (make-cont 3 t2 k))]
          [(car ,t)
           (cam-eval t v s (make-cont 5 k))]
          [(cdr ,t)
           (cam-eval t v s (make-cont 6 k))]
          [(,t0 ,t1)
           (cam-eval t0 v (cons v s) (make-cont 1 t1 k))]
          [,n (guard (integer? n))
              (cam-cont k (gamma n v) s)]
          [,x (error 'cam-eval (format "No match for ~s" x))])))
    (define cam-cont
      (trace-lambda applyk (k v s)
        (match k
          [(cont 1 (,t ,k))
           (let ((v^ (car s)))
             (cam-eval t v^ (cons v (cdr s)) (make-cont 2 k)))]
          [(cont 2 (,k))
           (let* ((c (car s))
                  (s (cdr s))
                  (v^ v)
                  (v (closv c))
                  (t (clost c)))
             (cam-eval t (make-pair v v^) s k))]
          [(cont 3 (,t1 ,k))
           (let ((v^ (car s)))
             (cam-eval t1 v^ (cons v (cdr s)) (make-cont 4 k)))]
          [(cont 4 (,k))
           (let ((v^ (car s)))
             (cam-cont k (make-pair v^ v) (cdr s)))]
          [(cont 5 (,k))
           (let ((v1 (fst v))
                 (v2 (snd v)))
             (cam-cont k v1 s))]
          [(cont 6 (,k))
           (let ((v1 (fst v))
                 (v2 (snd v)))
             (cam-cont k v2 s))]
          [(cont 0) v]
          [,x (error 'cam-count (format "No match for ~s" x))])))
    (cam-eval t (make-null) '() (make-cont 0))))

;; Test cases
;;(cam '(lambda 0))
;;(cam 'nil)
;;(cam '(cons nil nil))
;;(cam '((lambda 0) nil))
;;(cam '((lambda 0) (lambda 0)))
;;(cam '(car (cons nil (cons nil nil))))
;;(cam '(cdr (cons nil (cons nil nil))))

;; Church numerals
;;(define successor
;;  '(lambda (lambda (lambda (1 ((2 1) 0))))))

;;(define zero
;;  '(lambda (lambda 0)))

;;(define encode
;;  (lambda (n)
;;    (if (zero? n)
;;        zero
;;        `(,successor ,(encode (sub1 n))))))

;;(define decode
;;  (lambda (n)
;;    (match n
;;      (((lambda (lambda (lambda (1 (2 1) 0)))) ,n^)
;;       (add1 (decode n^)))
;;      ((lambda (lambda 0)) 0))))

;; Test cases
;;(cam (encode 0))
;;(cam `((,(encode 0) (lambda (cons nil 0))) nil))
;;(cam (encode 1))
;;(cam `((,(encode 1) (lambda (car 0))) (cons nil (cons nil nil))))
;;(cam `((,(encode 1) (lambda (cons nil 0))) nil))
;;(cam (encode 2))
;;(cam `((,(encode 2) (lambda (cons nil 0))) nil))

;;(define add
;;  '(lambda (lambda (lambda (lambda ((3 1) ((2 1) 0)))))))

;;(define to-list
;;  `(lambda ((0 (lambda (cons nil 0))) nil)))

;; A couple more test cases
;;(cam `(,to-list ,zero))
;;(cam `(,to-list ,(encode 1)))
;;(cam `(,to-list (,successor ,zero)))
;;(cam `(,to-list ,(encode 5)))

;;(cam `(,to-list ((,add ,(encode 2)) ,(encode 3))))

;; Omega - this will take a while.
;;'(cam `((lambda (0 0)) (lambda (0 0))))

;;(cam '(((lambda (lambda (cons 0 1))) nil) (lambda 0)))

;;(define mul
;;  '(lambda (lambda (lambda (lambda ((3 (2 1)) 0))))))

;;(cam `(,to-list ((,mul ,(encode 2)) ,(encode 3))))

;;(define pred
;;  '(lambda (lambda (lambda (((2 (lambda (lambda (0 (1 3))))) (lambda 1)) (lambda 0))))))

;;(define cam-length
;;  (lambda (n)
;;    (match n
;;      ((pair ,c ,d) (add1 (cam-length d)))
;;      (null 0))))

;;(cam-length (cam `(,to-list (,pred ,(encode 5)))))

;;(define fix
;;  '(lambda ((lambda (1 (lambda ((1 1) 0))))
;;       (lambda (1 (lambda ((1 1) 0)))))))

;;(define fact
;;  `(,fix (lambda (lambda ((0 (lambda ((,mul 1) (2 (,pred 1))))) ,(encode 1))))))

;;(cam-length (cam `(,to-list (,fact ,(encode 3)))))
