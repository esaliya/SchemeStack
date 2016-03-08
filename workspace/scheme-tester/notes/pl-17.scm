;----------------------------------------------------------------
; Registerization and Trampolining
; ---------------------------------------------------------------


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

; Test and expected lists
(define test-list-a '(1 2 3 8 9 8 7))
(define expected-list-a '(1 2 3 9 7))

(define test-list-b '(1 (2 3) (8 (9 (8) 7))))
(define expected-list-b '(1 (2 3) ((9 ()7))))


;----------------------------------------------------------------
; The good-old-style rember*8
; ---------------------------------------------------------------
(define rember*8
  (lambda (l)
    (cond
      [(null? l) '()]
      [(pair? (car l)) (cons (rember*8 (car l)) (rember*8 (cdr l)))]
      [(eq? (car l) 8) (rember*8 (cdr l))]
      [else (cons (car l) (rember*8 (cdr l)))])))

; test cases for the direct style rember*8
(test "direct-rember*8/a"
  (rember*8 test-list-a)
  expected-list-a)

(test "direct-rember*8/b"
  (rember*8 test-list-b)
  expected-list-b)
 

;----------------------------------------------------------------
; The cpsed rember*8, i.e. rember*8-cps
; ---------------------------------------------------------------
(define rember*8-cps
  (lambda (l k)
    (cond
      [(null? l) (k '())]
      [(pair? (car l)) (rember*8-cps (car l) (lambda (a) (rember*8-cps (cdr l) (lambda (d) (k (cons a d))))))]
      [(eq? (car l) 8) (rember*8-cps (cdr l) k)]
      [else (rember*8-cps (cdr l) (lambda (d) (k (cons (car l) d))))])))

; test cases for the cpsed rember*8-cps
(test "cpsed-rember*8-cps/a"
  (rember*8-cps test-list-a (lambda (v) v))
  expected-list-a)

(test "cpsed-rember*8-cps/b"
  (rember*8-cps test-list-b (lambda (v) v))
  expected-list-b)


;----------------------------------------------------------------
; The R.I. rember*8-cps, i.e. rember*8-cps-ri
; ---------------------------------------------------------------
(define rember*8-cps-ri
  (lambda (l k)
    (cond
      [(null? l) (apply-k k '())]
      [(pair? (car l)) (rember*8-cps-ri (car l) (outer-k l k))]
      [(eq? (car l) 8) (rember*8-cps-ri (cdr l) k)]
      [else (rember*8-cps-ri (cdr l) (inner-k (car l) k))])))

(define empty-k
  (lambda ()
    `(mt-k)))

(define inner-k
  (lambda (a k)
    `(inner-k ,a ,k)))

(define outer-k
  (lambda (l k)
    `(outer-k ,l ,k)))

(define apply-k
  (lambda (k v)
    (pmatch k
      [(mt-k) v]
      [(inner-k ,a ,k) (apply-k k (cons a v))]
      [(outer-k ,l ,k) (rember*8-cps-ri (cdr l) (inner-k v k))]))) 

; test cases for the R.I. rember*8-cps-ri
(test "R.I.-rember*8-cps-ri/a"
  (rember*8-cps-ri test-list-a (empty-k))
  expected-list-a)

(test "R.I.-rember*8-cps-ri/b"
  (rember*8-cps-ri test-list-b (empty-k))
  expected-list-b)


;----------------------------------------------------------------
; The registerized rember*8-cps-ri, i.e. rember*8-cps-ri-reg
; ---------------------------------------------------------------
; registers
(define *l*)
(define *k*)
(define *v*)

(define rember*8-cps-ri-reg
  (lambda () ; remember we originally had l and k as parameters
    (cond
      [(null? *l*) (begin (set! *k* *k*) (set! *v* '()) (apply-k-reg))] ; the tail call (apply-k) is like go-to
      [(pair? (car *l*)) (begin (set! *k* (outer-k *l* *k*)) (set! *l* (car *l*)) (rember*8-cps-ri-reg))]
      [(eq? (car *l*) 8) (begin (set! *k* *k*) (set! *l* (cdr *l*)) (rember*8-cps-ri-reg))]
      [else (begin (set! *k* (inner-k (car *l*) *k*)) (set! *l* (cdr *l*)) (rember*8-cps-ri-reg))])))

; No need to redefine the same data strucutral constructors for empty-k, inner-k, and outer-k
;;(define empty-k
;;  (lambda ()
;;    `(mt-k)))

;;(define inner-k
;;  (lambda (a k)
;;    `(inner-k ,a ,k)))

;;(define outer-k
;;  (lambda (l k)
;;    `(outer-k ,l ,k)))

(define apply-k-reg
  (lambda () ; remember we original had k and v as parameters
    (pmatch *k*
      [(mt-k) *v*]
      [(inner-k ,a ,k) (begin (set! *k* k) (set! *v* (cons a *v*)) (apply-k-reg))]
      [(outer-k ,l ,k) (begin (set! *k* (inner-k *v* k)) (set! *l* (cdr l)) (rember*8-cps-ri-reg))]))) 

; test cases for the R.I. rember*8-cps-ri
(test "registerized-rember*8-cps-ri-reg/a"
  (begin (set! *k* (empty-k)) (set! *l* test-list-a) (rember*8-cps-ri-reg))
  expected-list-a)

(test "registerized-rember*8-cps-ri-reg/b"
  (begin (set! *k* (empty-k)) (set! *l* test-list-b) (rember*8-cps-ri-reg))
  expected-list-b)



;----------------------------------------------------------------
; First driver program for the registerized rember*8-cps-ri-reg
; ---------------------------------------------------------------
(define rember*8-cps-ri-reg-driver-a
  (lambda (l)
    (begin
      (set! *k* (empty-k))
      (set! *l* l)
      (rember*8-cps-ri-reg))))

; test cases for first driver
(test "rember*8-cps-ri-reg-driver-a"
  (rember*8-cps-ri-reg-driver-a test-list-a)
  expected-list-a)

(test "rember*8-cps-ri-reg-driver-a"
  (rember*8-cps-ri-reg-driver-a test-list-b)
  expected-list-b)



;----------------------------------------------------------------
; Second driver program for the registerized rember*8-cps-ri-reg
; ---------------------------------------------------------------
; Introduce a register for program counter *pc*
(define *pc*)

(define rember*8-cps-ri-reg-b
  (lambda () ; remember we originally had l and k as parameters
    (cond
      [(null? *l*) (begin (set! *k* *k*) (set! *v* '()) (set! *pc* apply-k-reg-b) (*pc*))] ; the tail call (apply-k) is like go-to
      [(pair? (car *l*)) (begin (set! *k* (outer-k *l* *k*)) (set! *l* (car *l*)) (set! *pc* rember*8-cps-ri-reg-b) (*pc*))]
      [(eq? (car *l*) 8) (begin (set! *k* *k*) (set! *l* (cdr *l*)) (set! *pc* rember*8-cps-ri-reg-b) (*pc*))]
      [else (begin (set! *k* (inner-k (car *l*) *k*)) (set! *l* (cdr *l*)) (set! *pc* rember*8-cps-ri-reg-b) (*pc*))])))

(define apply-k-reg-b
  (lambda () ; remember we original had k and v as parameters
    (pmatch *k*
      [(mt-k) *v*]
      [(inner-k ,a ,k) (begin (set! *k* k) (set! *v* (cons a *v*)) (set! *pc* apply-k-reg-b) (*pc*))]
      [(outer-k ,l ,k) (begin (set! *k* (inner-k *v* k)) (set! *l* (cdr l)) (set! *pc* rember*8-cps-ri-reg-b) (*pc*))])))

(define rember*8-cps-ri-reg-driver-b
  (lambda (l)
    (begin
      (set! *k* (empty-k))
      (set! *l* l)
      (set! *pc* rember*8-cps-ri-reg-b)
      (*pc*))))

; test cases for second driver
(test "rember*8-cps-ri-reg-driver-b"
  (rember*8-cps-ri-reg-driver-b test-list-a)
  expected-list-a)

(test "rember*8-cps-ri-reg-driver-b"
  (rember*8-cps-ri-reg-driver-b test-list-b)
  expected-list-b)



;----------------------------------------------------------------
; Third driver program with trampoline for the registerized 
; rember*8-cps-ri-reg
; ---------------------------------------------------------------
(define rember*8-cps-ri-reg-c
  (lambda () ; remember we originally had l and k as parameters
    (cond
      [(null? *l*) (begin (set! *k* *k*) (set! *v* '()) (set! *pc* apply-k-reg-c))] ; the tail call (apply-k) is like go-to
      [(pair? (car *l*)) (begin (set! *k* (outer-k *l* *k*)) (set! *l* (car *l*)) (set! *pc* rember*8-cps-ri-reg-c))]
      [(eq? (car *l*) 8) (begin (set! *k* *k*) (set! *l* (cdr *l*)) (set! *pc* rember*8-cps-ri-reg-c))]
      [else (begin (set! *k* (inner-k (car *l*) *k*)) (set! *l* (cdr *l*)) (set! *pc* rember*8-cps-ri-reg-c))])))

(define apply-k-reg-c
  (lambda () ; remember we original had k and v as parameters
    (pmatch *k*
      [(mt-k, exit) (exit *v*)]
      [(inner-k ,a ,k) (begin (set! *k* k) (set! *v* (cons a *v*)) (set! *pc* apply-k-reg-c))]
      [(outer-k ,l ,k) (begin (set! *k* (inner-k *v* k)) (set! *l* (cdr l)) (set! *pc* rember*8-cps-ri-reg-c))])))

; We have to define a new empty-k-b
(define empty-k-exit
  (lambda (exit)
    `(mt-k ,exit)))

; Trampoline
(define trampoline
  (lambda ()
    (*pc*)
    (trampoline)))

(define rember*8-cps-ri-reg-driver-c
  (lambda (l)
    (call/cc (lambda (exit)
               (begin
                 (set! *k* (empty-k-exit exit))
                 (set! *l* l)
                 (set! *pc* rember*8-cps-ri-reg-c)
                 (trampoline))))))

; test cases for second driver
(test "rember*8-cps-ri-reg-driver-c"
  (rember*8-cps-ri-reg-driver-c test-list-a)
  expected-list-a)

(test "rember*8-cps-ri-reg-driver-c"
  (rember*8-cps-ri-reg-driver-c test-list-b)
  expected-list-b)
