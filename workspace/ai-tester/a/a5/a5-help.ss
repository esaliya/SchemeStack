;------------------------------------------------------------------------------
;; B551 - Fall 2010
;; Joey Kendall-Morwick <jmorwick@indiana.edu>
;; Assignment 5 - http://www.cs.indiana.edu/classes/b551-leak/hw5.html
;;
;; Extra code to assist with the homework.  Feel free to include 
;; any of this code within your assignment.  


;------------------------------------------------------------------------------
;; General helper procedures/macros

; macro which increments the value of a variable by 1
(define-syntax ++!
  (syntax-rules ()
    ((_ x) (set! x (+ x 1)))))


;------------------------------------------------------------------------------
; This procedure recursively calls f with succsessive values of ls 
; and the last accumulator value produced by f
;
; f:   a procedure that takes two arguments
; ls:  a list of first arguments for f
; acc: the initial accumulator (second argument for f)
;
;ex: (map-with-accumulator cons '(1 2 3) '())  ->  (3 2 1)
(define map-with-accumulator
  (lambda (f ls acc)
    (cond
      [(null? ls) acc]
      [else (map-with-accumulator f (cdr ls) (f (car ls) acc))])))

;determines if x is in list ls
(define contains?
  (lambda (x ls)
    (cond
      [(null? ls) #f]
      [(equal? x (car ls)) #t]
      [else (contains? x (cdr ls))])))

;produces the union of two sets
(define union
  (lambda (set1 set2)
    (cond
       [(null? set1) set2]
       [(contains? (car set1) set2)
         (union (cdr set1) set2)]
       [else (union (cdr set1) (cons (car set1) set2))])))

;replaces all instances of x with y within st
(define structure-replace
  (lambda (st x y)
    (cond
      [(equal? st x) y]
      [(pair? st) (map (lambda (subst) (structure-replace subst x y)) st)]
      [else st])))



;------------------------------------------------------------------------------
;; Assignment specific code


;creates a method for creating fresh variables
(define make-var-factory
  (lambda ()
    (let [(var-index 0)]
      (lambda ()
        (++! var-index)
        (string->symbol (string-append "?V" (number->string var-index) "*"))))))

;creates a fresh variable
(define var-factory (make-var-factory))

;determines whether or not something is a variable
(define var?
  (lambda (x)
    (and (symbol? x) (eq? (string-ref (symbol->string x) 0) #\? ))))

;returns all instances of variables within a sentence 
(define find-variables
  (lambda (st)
    (cond
      [(var? st) (list st)]
      [(pair? st) (union (find-variables (car st)) (find-variables (cdr st)))]
      [else '()])))

;replaces all variable instances with fresh variables
(define standardize-variables
  (lambda (st)
    (map-with-accumulator
      (lambda (var st) (structure-replace st var (var-factory)))
      (find-variables st)
      st)))

