;-----------------------------------------------------------------------------------------------------------
; This will copy a given list, even a nested one, to a new list
;-----------------------------------------------------------------------------------------------------------
(define copy
  (lambda (s)
    (cond
      [(null? s) '()]
      [(pair? (car s)) (cons (copy (car s)) (copy (cdr s)))]
      [else (cons (car s) (copy (cdr s)))])))

;-----------------------------------------------------------------------------------------------------------
; This is my clean innovation of the original cons-cell-count given in assignment 1
;-----------------------------------------------------------------------------------------------------------
(define cons-cell-count
  (lambda (ls)
    (cond     
      [(pair? ls) (add1 (+ (cons-cell-count (car ls)) (cons-cell-count (cdr ls))))]
      [else 0])))

;-----------------------------------------------------------------------------------------------------------
; I wanted to test if (random n) would give a value equal to n. So I wrote this little bugger to 
; test this recursively till it finds (random n) equals n. Hmm, it never came to an stop :). So I 
; had to put a limit 'u' to stop it. Anyway, with this I did a lazy guess that (random n) will not give n :)
;-----------------------------------------------------------------------------------------------------------
(define r
    (lambda (n s u)
      (let ([x (random n)])
        (cond
          [(eq? x n) x]
          [(eq? (length s) u) (cons x s)]
          [else (r n (cons x s) u)]))))
      