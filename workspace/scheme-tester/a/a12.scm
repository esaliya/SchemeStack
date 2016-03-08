;;----------------------------------
;; B521 - Assignment 10
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    0002560797
;; Email: sekanaya@indiana.edu
;;----------------------------------

;--------------------------------------------------------------------------------------
; Most of the code was readily available in the assignment itself
;--------------------------------------------------------------------------------------
;; miniKanren type inferencer

(load "a12-mkneverequalo.scm")
(load "a12-mkdefs.scm")
(load "matche.scm")

;; Test macro

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


;; Use unification with occur check:
;; (== `(,x) x) fails.
(define == ==-check)

(define parse
  (lambda (e)
    (cond
      [(symbol? e) `(var ,e)]
      [(number? e) `(intc ,e)]
      [(boolean? e) `(boolc ,e)]
      [else
       (case (car e)
         [(sub1) `(sub1 ,(parse (cadr e)))]
         [(+) `(+ ,(parse (cadr e)) ,(parse (caddr e)))]
         [(*) `(* ,(parse (cadr e)) ,(parse (caddr e)))]
         [(zero?) `(zero? ,(parse (cadr e)))]
         ; ------------------------------------------------------------------------
         ; I did this :)
         [(cons) `(cons ,(parse (cadr e)) ,(parse (caddr e)))]
         ;-------------------------------------------------------------------------
         [(if) `(if ,(parse (cadr e)) ,(parse (caddr e)) ,(parse (cadddr e)))]
         [(lambda) `(lambda ,(cadr e) ,(parse (caddr e)))]
         [(fix) `(fix ,(parse (cadr e)))]
         [else `(app ,(parse (car e)) ,(parse (cadr e)))])])))

(define unparse
  (lambda (e)
    (if (var? e) e
      (case (car e)
        [(var) e]
        [(intc) e]
        [(boolc) e]
        [(sub1) `(sub1 ,(unparse (cadr e)))]
        [(+) `(+ ,(unparse (cadr e)) ,(unparse (caddr e)))]
        [(*) `(* ,(unparse (cadr e)) ,(unparse (caddr e)))]
        [(zero?) `(zero? ,(unparse (cadr e)))]
        [(if) `(if ,(unparse (cadr e))
                 ,(unparse (caddr e))
                 ,(unparse (cadddr e)))]
        [(lambda) `(lambda ,(cadr e) ,(unparse (caddr e)))]
        [(fix) `(fix ,(unparse (cadr e)))]
        [(app) `(,(unparse (cadr e)) ,(unparse (caddr e)))]))))

(define !-o
  (lambda (gamma e t)
    (matche `(,gamma ,e ,t)
            [(,gamma (intc ,n) int)]
            [(,gamma (boolc ,b) bool)]
            [(,gamma (zero? ,e) bool)
             (!-o gamma e 'int)]
            [(,gamma (sub1 ,e) int)
             (!-o gamma e 'int)]
            [(,gamma (+ ,e1 ,e2) int)
             (!-o gamma e1 'int)
             (!-o gamma e2 'int)]
            [(,gamma (* ,e1 ,e2) int)
             (!-o gamma e1 'int)
             (!-o gamma e2 'int)]
            [(,gamma (if ,test ,conseq ,alt) ,t)
             (!-o gamma test 'bool)
             (!-o gamma conseq t)
             (!-o gamma alt t)]
            [(,gamma (fix ,rand) ,type)
             (!-o gamma rand `(-> ,type ,type))]
            ; ------------------------------------------------------------------------
            ; I did this :)
            [(,gamma (var ,x) ,tx)
             (lookupo x gamma tx)]
            [(,gamma (lambda (,x) ,body) (-> ,tx ,tbody))
             (!-o `((,x . ,tx) . ,gamma) body tbody)]
            [(,gamma (app ,rator ,rand) ,tapp)
             (exist (trand)
               (!-o gamma rator `(-> ,trand ,tapp))
               (!-o gamma rand trand))]
            [(,gamma (cons ,a ,d) (pairof ,ta ,td))
             (!-o gamma a ta)
             (!-o gamma d td)]
            ; ------------------------------------------------------------------------
            
            )))

(define lookupo
  (lambda (x gamma type)
    (exist (y t rest)
      (== `((,y . ,t) . ,rest) gamma)
      (conde
        ((== x y) (== type t))
        ;; (=/= x y) is a disequality constraint, asserting that x and
        ;; y can never be unified
        ((=/= x y) (lookupo x rest type))))))

;--------------------------------------------------------------------------------------
; Test cases for the type inferencer
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for the type inferencer\n=================================================\n")


(test "1"
  (run* (q) (!-o '() '(intc 17) q))
  '(int))

(test "2"
  (run* (q) (!-o '() '(zero? (intc 24)) q))
  '(bool))

(test "3"
  (run* (q) (!-o '() '(zero? (sub1 (intc 24))) q))
  '(bool))

(test "4"
  (run* (q)
    (!-o '() '(zero? (sub1 (sub1 (intc 18)))) q))
  '(bool))

(test "5"
  (run* (q)
    (!-o '() (parse '(lambda (n) (if (zero? n) n n))) q))
  '((-> int int)))

(test "6"
  (run* (q)
    (!-o '() (parse '((lambda (n) (zero? n)) 5)) q))
  '(bool))

(test "7"
  (run* (q)
    (!-o '() '(if (zero? (intc 24)) (intc 3) (intc 4)) q))
  '(int))

(test "8"
  (run* (q)
    (!-o '() '(if (zero? (intc 24)) (zero? (intc 3)) (zero? (intc 4))) q))
  '(bool))

(test "9"
  (run* (q)
    (!-o '() '(lambda (x) (sub1 (var x))) q))
  '((-> int int)))

(test "10"
  (run* (q)
    (!-o '() '(lambda (a) (lambda (x) (+ (var a) (var x)))) q))
  '((-> int (-> int int))))

(test "11"
  (run* (q)
    (!-o '() (parse '(lambda (f)
                       (lambda (x)
                         ((f x) x))))
         q))
  '((->
     (-> _.0 (-> _.0 _.1))
     (-> _.0 _.1))))

(test "12"
  (run* (q)
    (!-o '() (parse '(sub1 (sub1 (sub1 6)))) q))
  '(int))

(test "13"
  (run 1 (q)
       (exist (t)
         (!-o '() (parse '(lambda (f) (f f))) t)))
  '())

(test "14"
  (let ([v (run 20 (q)
                (exist (lam a b)
                  (!-o '() `(app (,lam (,a) ,b) (intc 5)) 'int)
                  (== `(,lam (,a) ,b) q)))])
    (pretty-print v)
    (length v))
  20)

(test "15"
  (let ([v (run 30 (q)
                (!-o '() q 'int))])
    (pretty-print v)
    (length v))
  30)

(test "16"
  (let ([v (run 30 (q)
                (!-o '() q '(-> int int)))])
    (pretty-print v)
    (length v))
  30)

(test "17"
  (let ([v (run 30 (q)
                (!-o '() q '(-> bool int)))])
    (pretty-print v)
    (length v))
  30)

(test "18"
  (let ([v (run 30 (q)
                (!-o '() q '(-> int (-> int int))))])
    (pretty-print v)
    (length v))
  30)

(test "19"
  (let ([v (run 100 (q)
                (exist (e t)
                  (!-o '() e t)
                  (== `(,e ,t) q)))])
    (pretty-print v)
    (length v))
  100)

(test "20"
  (let ([v (run 100 (q)
                (exist (g e t)
                  (!-o g e t)
                  (== `(,g ,e ,t) q)))])
    (pretty-print v)
    (length v))
  100)

(test "21"
  (length
   (run 100 (q)
        (exist (g v)
          (!-o g `(var ,v) 'int)
          (== `(,g ,v) q))))
  100)

(test "22"
  (run 1 (q)
       (exist (g)
         (!-o g
              (parse '((fix (lambda (!)
                              (lambda (n)
                                (if (zero? n)
                                  1
                                  (* n (! (sub1 n)))))))
                       5))
              q)))
  '(int))

;; The following test demonstrates an interesting property: just
;; because a program typechecks doesn't mean it will terminate.

;; (define fix
;;  (lambda (f)
;;    (letrec ([g (lambda (x)
;;                  ((f g) x))])
;;      g)))

(test "23"
  (run 1 (q)
       (exist (g)
         (!-o g
              (parse '((fix (lambda (!)
                              (lambda (n)
                                (* n (! (sub1 n))))))
                       5))
              q)))
  '(int))

(printf "\n=================================================\nTests cases for the warm up brain teaser\n=================================================\n")
(test "pair-1"
  (run* (q) (!-o '() (parse '(cons (zero? 1) (zero? 0))) q))
  '((pairof bool bool)))

(test "pair-2"
  (run* (q) (!-o '() (parse '(cons (zero? 1) (cons (zero? 1) (zero? 0)))) q))
  '((pairof bool (pairof bool bool))))

(test "pair-3"
  (run* (t) (!-o '() (parse '(lambda (x) (cons x x))) t))
  '((-> _.0 (pairof _.0 _.0))))

(test "pair-4"
  (run* (t) (!-o '() (parse '(lambda (x)
                               (lambda (y) (cons (zero? x) (+ x y))))) t))
  '((-> int (-> int (pairof bool int)))))

