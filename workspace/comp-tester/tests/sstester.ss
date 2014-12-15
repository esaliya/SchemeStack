(define f
  (lambda ()
    10))

(define len
  (lambda (ls)
    (cond
     [(null? ls) 0]
     [else (add1 (len (cdr ls)))])))

(define cats
  (lambda (s)
    (define f
      (lambda (e)
        (match e
          [(wow ,[g -> x* ...]) x*])))
    (define g
      (lambda (e)
        (reverse e)))
    (f s)))

(define simple
  (lambda (s)
    (match s
      [(,[simple -> x ...] ,y) `(,y ,x)]
      [,z 'boom])))

(case-sensitive #t)

(define mt
  (lambda (s)
    (define Prg
      (lambda (p)
        (match s
          [(letrec ,tail)
           `(code ,(Tail tail) ... ...)])))
    (define Tail
      (lambda (t)
        '((bing boy) (sing song))))
    (Prg s)))

;;      (printf "\n*************\n~s\n*************\n" ef)
;; 

(lambda (x) (if (eq? (modulo x 2) 0) x 0))
        