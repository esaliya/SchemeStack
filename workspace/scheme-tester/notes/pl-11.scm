
;Tranformation of expressions like
(f (g ( h  (a  (b x y) (z w) r ) (s t)) u) )
               ------  ----
;              What runs first -- scheme doens't say

; -- just say left most inner most one is resolved first               
(f (g ( h  (a  (b x y) (z w) r ) (s t)) u)) 
;              ------ 
;             become v
(b x y (lambda (v) (f (g (h (a v (z w)) r) (s t)) u)))
                   ; incomplete now -- missing free var k

;Just takes in a flat list and removes all even numbers
(define multirmber-even ;mult-rm-er
  (lambda (ls)
    (cond 
      ((null? ls) '())
      ((even? (car ls)) (multirmber-even (cdr ls)))
      (else (cons (car ls) (multirmber (cdr ls)))))))

;Job in life is to protect against inf loops
; if ls is a circluar list -- never ends
(define multirmber-even ;mult-rm-er
  (lambda (ls k)
    (cond 
      ((null? ls) '(k '())) ;When you are done -- invoke k
      ((even? (car ls)) (multirmber-even (cdr ls) (lambda (v) (k v))))
      (else (cons (car ls) (multirmber (cdr ls)) (lambda (v)(k (cons (car ls) v ))))))))

 (multirmber-even -> me)
 (me '(1 2 3 4 5) (lambda (v) v))
; let's call (lambda (v) v) ID
 (me '(2 3 4 5) (lambda (v) ID (cons 1 v)))     
; let's call (lambda (v) ID (cons 1 v)) a     
 (me '(3 4 5) (lambda (v) a v))     
; let's call (lambda (v) a) b     
 (me '(4 5) (lambda (v) b (cons 3 v)))     
; let's call (lambda (v) b) g     
 (me '(5) (lambda (v) g v))
; let's call (lambda (v) g v) d
 (me '() (lambda (d (cons 5 v))))
call d
(g (5)
(a (3 5))
(id (1 3 5))
(1 3 5)
;All call are tail-recursive as a side-effect

(define a 
  (lambda

  (lambda (b) -- boolean

;Example 2
(define !
  (lambda (n)
    (if (zero? n)
      1
      (* n (! (sub1 n))))))
      
(define _!
  (lambda (n)
    (if (zero? n)
      (k 1)
      (_! (sub1 n) (lambda (v) (k (* n v)))))))
      
;test on fact 5
;Don't forget to name continuations so that things don't get ugly
(_! 5 (lambda (v) v))

;tail calls can be translated directly since
(lambda (v) v k) -> k
;CPS 
(define __!
    (lambda (n c k)
        (if (zero? n)
              (c 1 k)
                    (__! (sub1 n) (lambda (v k) (c (* n v) k )) k))))
(__! 5 (lambda (v k)(k v)) (lambda(q) q))