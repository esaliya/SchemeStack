;;8. Here is a box-and-pointer diagram of a Scheme value consisting of
;;   a pair whose car is the fixnum 7 and whose cdr is a closure with one
;;   free variable whose value is the fixnum 3.

;;   pair                  closure
;;   +-------+-------+     +-------+-------+
;;   |   7   |   x---+---->|   x   |   3   |
;;   +-------+-------+     +---+---+-------+
;;                             |
;;                             v
;;                            code

;;   A Scheme expression that produces this value is

;;     (let ([a 3]) (cons 7 (lambda () a)))

;;   Consider the second box-and-pointer diagram below:

;;      procedure             procedure
;;      +-------+-------+     +-------+-------+-------+
;;   +->|   x   |   x---+---->|   x   |   x   |   x   |
;;   |  +---+---+-------+     +---+---+---+---+---+---+
;;   |      |                     |       |       |
;;   |      v                     v       |       |
;;   |     code                  code     |       v
;;   +------------------------------------+       +-------+-------+
;;                                                |   3   |   ()  |
;;                                                +-------+-------+
;;                            
;;   Write down a source-language expression that evaluates to the value
;;   illustrated by the second diagram.

;;   Assume that no challenge-assignment passes are run.

(let ([p (cons 3 ())])
  (letrec ([f (lambda (p) (if (eq? (car p) 3) p (g)))]
           [g (lambda () (f p))])
    (g)))

;;--------

;;9. Consider the following nonterminating UIL program.

;;   (letrec ([f$2 (lambda (cp.5 x.3)
;;                   (locals ()
;;                     (begin
;;                       (mset! (mref cp.5 14) -1
;;                         (- 0 (mref (mref cp.5 14) -1)))
;;                       (f$2 (mref cp.5 6)
;;                            (+ x.3 (mref (mref cp.5 14) -1))))))])
;;     (locals (y.4 y.1 t.7 t.8 t.9 f.2 t.6)
;;       (begin
;;         (set! y.4 8)
;;         (set! y.1
;;           (begin
;;             (set! t.7 y.4)
;;             (set! t.8 30)
;;             (set! t.9 (+ (alloc 16) 1))
;;             (mset! t.9 -1 t.7)
;;             (mset! t.9 7 t.8)
;;             t.9))
;;         (set! f.2
;;           (begin
;;             (set! t.6 (+ (alloc 24) 2))
;;             (mset! t.6 -2 f$2)
;;             t.6))
;;         (mset! f.2 6 f.2)
;;         (mset! f.2 14 y.1)
;;         (f$2 f.2 136))))

;;   Write down a source-language program for which the week 15 online
;;   compiler (with default settings) produces the UIL program above. 
;;   (Your compiler should produce a similar UIL program with the
;;   standard helpers.ss object-layout definitions.)

(let ([y 1])
  (let ([y (cons y '(void))])
    (letrec ([f (lambda (x)
                  (set-car! y (- 0 (car y)))
                  (f (+ x (car y))))])
      (f 17))))
                  

;;--------
 
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                  
                                                  
                                                  