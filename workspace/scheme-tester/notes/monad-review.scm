;--------------------------------------------------------------------------------------
; Store Monad Definition
;--------------------------------------------------------------------------------------
(define unit_store ; a -> Ma
  (lambda (a) 
    (lambda (s)     ;; <-------------------- this lambda is a Ma                
      `(,a . ,s))))
 
(define star_store ; (a->Ma) -> (Ma -> Ma)
  (lambda (f) ; f: a -> Ma
    (lambda (Ma)
      (lambda (s)   ;; <-------------------- this lambda is a Ma                
        (let ((p (Ma s)))
          (let ((new-a (car p)) (new-s (cdr p)))
            (let ((new-Ma (f new-a)))
              (new-Ma new-s))))))))

;--------------------------------------------------------------------------------------
; CPS Monad Definition
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

;--------------------------------------------------------------------------------------
; Direct style copy-list
(define copy-list
  (lambda (ls)
    (cond
      [(null? ls) '()]
      [(pair? (car ls)) (cons (copy-list (car ls)) (copy-list (cdr ls)))]
      [else (cons (car ls) (copy-list (cdr ls)))]))) 
;--------------------------------------------------------------------------------------

; Now CPS version
(define copy-list-cps
  (lambda (ls k)
    (cond
      [(null? ls) (k '())]
      [(pair? (car ls)) (copy-list-cps (car ls) (lambda (a) (copy-list-cps (cdr ls) (lambda (d) (k (cons a d))))))]
      [else (copy-list-cps (cdr ls) (lambda (d) (k (cons (car ls) d))))]))) 
;--------------------------------------------------------------------------------------

; Some note on pure/natural values: the ultimate value (um, value types rather) we are interested in
; Another note:
;   (bind Ma f) = ((star f) Ma)
;--------------------------------------------------------------------------------------

; Now the monadic style: we call this as ((copy-monadic '(a (b) c)) 0)
; Okay fix this :)
(define copy-monadic
  (lambda (ls)
    (cond
      [(null? ls) (unit_store '())]
      [(pair? (car ls)) ((star_store (lambda (d) ((star_store (lambda (a) (unit_store (cons a d))))
                                            (copy-monadic (car ls)))))
                   (copy-monadic (cdr ls)))]
      [else ((star_store (lambda (d) (unit_store (cons (car ls) d))))
             (copy-monadic (cdr ls)))])))

;--------------------------------------------------------------------------------------
; a-10: binaryXdecimal -> ((binaryXdecimal '(0 0 1)) 0) -> '((0 0 1) . 4)
; Hmm, I could have used pmatch version in my code, but that's my code :D
; Also you can use cond instead of pmatch
(define binaryXdecimal
  (lambda (ls)
    (pmatch ls
      [() (unit_store '())]
      [(0 . ,d) ((star_store (lambda (a)
                               ((star_store (lambda (d)
                                              (unit_store ls)))
                                (lambda (s) `(__ . ,(* 2 s))))))
                 (binaryXdecimal d))]
      [(1 . d) ((star_store (lambda (a)
                              ((star_store (lambda (d)
                                             (unit_store ls)))
                               (lambda (s) `(__ . (+ 1 (*2 s)))))))
                (binaryXdecimal d))])))

;--------------------------------------------------------------------------------------
; Natural monad (Prof. Dan's word). Others call it identity monad.
(define unit_id
  (lambda (a)
    a))
                               
                               

