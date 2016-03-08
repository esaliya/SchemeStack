;;----------------------------------
;; B521 - Assignment 6
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    0002560797
;; Email: sekanaya@indiana.edu
;;----------------------------------
 
;----------------------------------------------------------------
;; Something I grab from Fall 2010 class.
;----------------------------------------------------------------
;;(define rember*1
;;  (lambda (ls)
;;    (cond
;;      [(null? ls) '()]
;;      [(pair? (car ls))
;;       (cond
;;         [(equal? (car ls) (rember*1 (car ls)))
;;          (cons (car ls) (rember*1 (cdr ls)))]
;;         [else (cons (rember*1 (car ls)) (cdr ls))])]
;;      [(eq? (car ls) '?) (cdr ls)]
;;      [else (cons (car ls) (rember*1 (cdr ls)))])))

(define rember*1
  (lambda (ls k)
    (cond
      [(null? ls) (k '())]
      [(pair? (car ls))
       (rember*1 (car ls) (lambda (v) (cond
                                        [(equal? (car ls) v) (rember*1 (cdr ls) (lambda (v) (k (cons (car ls) v))))]
                                        [(rember*1 (car ls) (lambda (v) (k (cons v (cdr ls)))))])))]
      [(eq? (car ls) '?) (k (cdr ls))]
      [else (rember*1 (cdr ls) (lambda (v) (k (cons (car ls) v))))])))

;; Another nice one. See your pascal example as well. Also see tests/Fall2010.scm for possible mistake as well.
;; 
;;(define M
;;  (lambda (f)
;;    (lambda (ls)
;;      (cond
;;        ((null? ls) '())
;;        (else (cons (f (car ls)) ((M f) (cdr ls))))))))

;;>((M add1) '(1 2 3))


(define M
  (lambda (f k)
    (k (lambda (ls c)
         (cond
           ((null? ls) (c '()))
           (else (M f (lambda (g) (g (cdr ls) (lambda (l) (c (cons (f (car ls)) l))))))))))))

;;>(M add1 (lambda (g) (g '(1 2 3) (lambda (x) x)))) 
;----------------------------------------------------------------


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
; empty-k procedure, taken happily from the assignment itself :)
;--------------------------------------------------------------------------------------
(define empty-k 
  (lambda ()
    (let ([okay #t])
      (lambda (v)
        (if okay
            (begin
              (set! okay #f)
              v)
            (error 'empty-k "k invoked in non-tail position"))))))

;--------------------------------------------------------------------------------------
; non cps version of length
;--------------------------------------------------------------------------------------
;;(define length
;;  (lambda (ls)
;;    (cond
;;      [(null? ls) 0]
;;      [else (add1 (length (cdr ls)))])))
;--------------------------------------------------------------------------------------

;--------------------------------------------------------------------------------------
; cps version of length, i.e. length-cps
;--------------------------------------------------------------------------------------
(define length-cps
  (lambda (ls k)
    (cond
      [(null? ls) (k 0)]
      [else (length-cps (cdr ls) (lambda (v) (k (add1 v))))])))
;--------------------------------------------------------------------------------------



;--------------------------------------------------------------------------------------
; non cps version of count-syms*
;--------------------------------------------------------------------------------------

;;(define count-syms*
;;  (lambda (ls)
;;    (cond
;;      [(null? ls) 0]
;;      [(pair? (car ls)) (+ (count-syms* (car ls)) (count-syms* (cdr ls)))]
;;      [(symbol? (car ls)) (add1 (count-syms* (cdr ls)))]
;;      [else (count-syms* (cdr ls))])))
;--------------------------------------------------------------------------------------

;--------------------------------------------------------------------------------------
; cps version of count-syms*, i.e. count-syms*-cps
;--------------------------------------------------------------------------------------
(define count-syms*-cps
  (lambda (ls k)
    (cond
      [(null? ls) (k 0)]
      [(pair? (car ls)) (count-syms*-cps (car ls) (lambda (v) (count-syms*-cps (cdr ls) (lambda (x) (k (+ v x))))))]
      [(symbol? (car ls)) (count-syms*-cps (cdr ls) (lambda (v) (k (add1 v))))]
      [else (count-syms*-cps (cdr ls) k)])))
;--------------------------------------------------------------------------------------



;--------------------------------------------------------------------------------------
; non cps version of tree-sum
;--------------------------------------------------------------------------------------

;;(define tree-sum
;;  (lambda (ls)
;;    (cond
;;      [(null? ls) 0]
;;      [(pair? (car ls))
;;       (+ (tree-sum (car ls))
;;          (tree-sum (cdr ls)))]
;;      [else (+ (car ls) (tree-sum (cdr ls)))])))
;--------------------------------------------------------------------------------------

;--------------------------------------------------------------------------------------
; cps version of tree-sum, i.e. tree-sum-cps
;--------------------------------------------------------------------------------------
(define tree-sum-cps
  (lambda (ls k)
    (cond
      [(null? ls) (k 0)]
      [(pair? (car ls)) (tree-sum-cps (car ls) (lambda (v) (tree-sum-cps (cdr ls) (lambda (x) (k (+ v x))))))]
      [else (tree-sum-cps (cdr ls) (lambda (v) (k (+ (car ls) v))))])))
;--------------------------------------------------------------------------------------



;--------------------------------------------------------------------------------------
; non cps version of walk, (this is already tail recursive)
;--------------------------------------------------------------------------------------
;;(define walk
;;  (lambda (v ls)
;;    (cond
;;      [(symbol? v)
;;       (let ((p (assq v ls)))
;;         (cond
;;           [p (walk (cdr p) ls)]
;;           [else v]))]
;;      [else v])))
;--------------------------------------------------------------------------------------

;--------------------------------------------------------------------------------------
; cps version of walk, i.e. walk-cps
;--------------------------------------------------------------------------------------
(define walk-cps
  (lambda (v ls k)
    (cond
      [(symbol? v) (let ([p (assq v ls)])
                     (cond
                       [p (walk-cps (cdr p) ls k)]
                       [else (k v)]))]
      [else (k v)])))
;--------------------------------------------------------------------------------------



;--------------------------------------------------------------------------------------
; non cps version of ack
;--------------------------------------------------------------------------------------
;;(define ack
;;  (lambda (m n)
;;    (cond
;;      [(zero? m) (add1 n)]
;;      [(zero? n) (ack (sub1 m) 1)]
;;      [else (ack (sub1 m)
;;                 (ack m (sub1 n)))])))
;--------------------------------------------------------------------------------------

;--------------------------------------------------------------------------------------
; cps version of ack, ack-cps
;--------------------------------------------------------------------------------------
(define ack-cps
  (lambda (m n k)
    (cond
      [(zero? m) (k (add1 n))]
      [(zero? n) (ack-cps (sub1 m) 1 k)]
      [else (ack-cps m (sub1 n) (lambda (v) (ack-cps (sub1 m) v k)))])))
;--------------------------------------------------------------------------------------



;--------------------------------------------------------------------------------------
; non cps version of every?
;--------------------------------------------------------------------------------------
;;(define every?
;;  (lambda (pred ls)
;;    (if (null? ls)
;;        #t
;;        (if (pred (car ls))
;;            (every? pred (cdr ls))
;;            #f))))
;--------------------------------------------------------------------------------------

;--------------------------------------------------------------------------------------
; cps version of every?, i.e. every?-cps
;--------------------------------------------------------------------------------------
(define every?-cps
  (lambda (pred ls k)
    (if (null? ls)
      (k #t)
      (pred (car ls) (lambda (v) (if v (every?-cps pred (cdr ls) k) (k #f))))))) 

; test predicates for every?-cps
;---------------------------------
; a cps predicate to check if a given number is binary
(define binary?
    (lambda (n k)
      (cond
        [(zero? n) (k #t)]
        [(zero? (sub1 n)) (k #t)]
        [else (k #f)])))

; a cps predicate to check if a given number, n, is the factorial of some number, m
; I came up with this predicate and I could improve it if I knew how to check if 
; a number contains decimal points.
(define  factorial?
  (lambda (n k)
    (letrec ([f (lambda (n d k)
                  (cond
                    [(eq? n 1) (k #t)]
                    [(< n 1) (k #f)]
                    [else (f (/ n d) (+ 1 d) k)]))])
      (f n 2 k))))
;--------------------------------------------------------------------------------------



;--------------------------------------------------------------------------------------
; non cps version of fact
;--------------------------------------------------------------------------------------
;;(define fact
;;  (lambda (n)
;;    ((lambda (f-gen)
;;       (f-gen f-gen n))
;;     (lambda (fact n)
;;       (cond
;;         [(zero? n) 1]
;;         [else (* n (fact fact (sub1 n)))])))))
;--------------------------------------------------------------------------------------

;--------------------------------------------------------------------------------------
; cps version of fact, i.e. fact-cps
;--------------------------------------------------------------------------------------
(define fact-cps
  (lambda (n k)
    ((lambda (f-gen)
       (f-gen f-gen n k))
     (lambda (fact n d)
       (cond
         [(zero? n) (d 1)]
         [else (fact fact (sub1 n) (lambda (v) (d (* n v))))])))))
;--------------------------------------------------------------------------------------



;--------------------------------------------------------------------------------------
; non cps version of pascal
;--------------------------------------------------------------------------------------
;;(define pascal
;;  (lambda (n)
;;    (let ((pascal
;;           (lambda (pascal)
;;             (lambda (m a)
;;               (cond
;;                 [(> m n) '()]
;;                 [else (let ((a (+ a m)))
;;                         (cons a ((pascal pascal) (add1 m) a)))])))))
;;      ((pascal pascal) 1 0))))
;--------------------------------------------------------------------------------------

;--------------------------------------------------------------------------------------
; cps version of pascal, i.e. pascal-cps
;--------------------------------------------------------------------------------------
(define pascal-cps
  (lambda (n k)
    (let ([pascal
           (lambda (pascal c)
             (c (lambda (m a t)
                  (cond
                    [(> m n) (t '())]
                    [else (let ([a (+ a m)])
                            (pascal pascal (lambda (f) (f (add1 m) a (lambda (v) (t (cons a v)))))))]))))])
      (pascal pascal (lambda (f) (f 1 0 k))))))
;--------------------------------------------------------------------------------------



;--------------------------------------------------------------------------------------
; Test cases for the cps functions
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for the cps functions\n=================================================\n")

(test "length-cps 1"
  (length-cps '(1 3 4 0 88 45) (empty-k))
  6)

(test "length-cps 2"
  (length-cps '() (empty-k))
  0)

(test "length-cps 3"
  (length-cps '(()) (empty-k))
  1)

(test "count-syms*-cps 1"
  (count-syms*-cps '(1 2 x y 3 b 9) (empty-k))
  3)

(test "count-syms*-cps 2"
  (count-syms*-cps '(2 3 4 5 6 7) (empty-k))
  0)

(test "count-syms*-cps 3"
  (count-syms*-cps '() (empty-k))
  0)

(test "tree-sum-cps 1"
  (tree-sum-cps '(1 2 3 45) (empty-k))
  51)

(test "tree-sum-cps 2"
  (tree-sum-cps '() (empty-k))
  0)

(test "tree-sum-cps 3"
  (tree-sum-cps '(1 2 (3 4) (5 6 (7 (8)))) (empty-k))
  36)

(test "walk-cps 1"
  (walk-cps 'a '((a . b) (b . 9) (c . 10)) (empty-k))
  9)

(test "walk-cps 2"
  (walk-cps 'c '((a . b) (b . 9) (c . 10)) (empty-k))
  10)

(test "walk-cps 3"
  (walk-cps 'b '((a . b) (b . 9) (c . 10)) (empty-k))
  9)

(test "ack-cps 1"
  (ack-cps 2 3 (empty-k))
  9)

(test "ack-cps 2"
  (ack-cps 3 3 (empty-k))
  61)

(test "ack-cps 3"
  (ack-cps 4 0 (empty-k))
  13)

(test "every?-cps 1" 
  (every?-cps binary? '(1 0 1 0 1 0 0 1 0 1 0) (empty-k))
  #t)

(test "every?-cps 2" 
  (every?-cps binary? '(1 3 1 0 1 0 0 1 0 1 0) (empty-k))
  #f)

(test "every?-cps 3" 
  (every?-cps binary? '() (empty-k))
  #t)

(test "every?-cps 4" 
  (every?-cps factorial? '(1 2 6 24 120 720 5040) (empty-k))
  #t)

(test "every?-cps 5" 
  (every?-cps factorial? '(1 60 120 720 5040) (empty-k))
  #f)

(test "fact-cps 1"
  (fact-cps 4 (empty-k))
  24)

(test "fact-cps 2"
  (fact-cps 0 (empty-k))
  1)

(test "fact-cps 3"
  (fact-cps 7 (empty-k))
  5040)

(test "pascal-cps 1"
  (pascal-cps 0 (empty-k))
  '())

(test "pascal-cps 2"
  (pascal-cps 3 (empty-k))
  '(1 3 6))

(test "pascal-cps 3"
  (pascal-cps 10 (empty-k))
  '(1 3 6 10 15 21 28 36 45 55))

;--------------------------------------------------------------------------------------
; Brainteaser
;--------------------------------------------------------------------------------------
; still working on it. I am not sure if I would be able to make it by today, but it (the problem) really is cool





