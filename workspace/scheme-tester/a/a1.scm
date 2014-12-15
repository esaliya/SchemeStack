(define increment
  (lambda (s)
    (cond
      [(null? s) '()]
      [(pair? (car s)) (append (list (increment (car s))) (increment (cdr s)))]
      [else (cons (add1 (car s)) (increment (cdr s)))])))

(define insertL
  (lambda (x y s)
    (cond
      [(null? s) '()]
      [(eq? x (car s)) (cons y (cons x (insertL x y (cdr s))))]
      [else (cons (car s) (insertL x y (cdr s)))])))

(define last-eq?
  (lambda (x s)
    (condt
      [(null? (cdr s)) (cond
                         [(eq? x (car s)) #t]
                         [else #f])]
      [else (last-eq? x (cdr s))])))

(define remove
  (lambda (x s)
    (cond
      [(null? s) '()]
      [(eq? x (car s)) (remove x (cdr s))]
      [else (cons (car s) (remove x (cdr s)))])))

(define count-between
  (lambda (x y)
    (cond
      [(eq? y x) '()]
      [else (cons x (count-between (add1 x) y))])))

(define occurs
  (lambda (x s)
    (cond
      [(null? s) 0]
      [(eq? (car s) x) (+ 1 (occurs x (cdr s)))]
      [else (occurs x (cdr s))])))

(define filter
  (lambda (p s)
    (cond
      [(null? s) '()]
      [(p (car s)) (cons (car s) (filter p (cdr s)))]
      [else (filter p (cdr s))])))

(define zip
  (lambda (s1 s2)
    (cond
      [(null? s1) '()]
      [else (cons (list (car s1) (car s2)) (zip (cdr s1) (cdr s2)))])))

(define sum-to
  (lambda (x)
    (cond 
      [(eq? x 1) 1]
      [else (+ x (sum-to (sub1 x)))])))

(define map
  (lambda (p s)
    (cond
      [(null? s) '()]
      [else (cons (p (car s)) (map p (cdr s)))])))

(define append
  (lambda (s1 s2)
    (cond
      [(null? s1) s2]
      [else (cons (car s1) (append (cdr s1) s2))])))

(define reverse
  (lambda (s)
    (cond
      [(null? s) '()]
      [else (append (reverse (cdr s)) (list (car s)))])))

; A good way to handle reverse - added 12/9/9
(define reverse
  (lambda (l)
    (cond
      [(null? l) '()]
      [(pair? (car l)) (append (reverse (cdr l)) (cons (reverse (car l)) '()))]
      [else (append (reverse (cdr l)) (cons (car l) '()))])))

(define fact
  (lambda (x)
    (cond
      [(eq? x 0) 1]
      [else (* x (fact (sub1 x)))])))

(define count-symbols
  (lambda (s)
    (cond
      [(null? s) 0]
      [(symbol? (car s)) (add1 (count-symbols (cdr s)))]
      [else (+ (count-symbols (car s)) (count-symbols (cdr s)))])))

(define fib
  (lambda (x)
    (cond
      [(eq? x 0) 0]
      [(eq? x 1) 1]
      [else (+ (fib (sub1 x)) (fib (sub1 (sub1 x))))])))

(define even-layers?
  (lambda (s)
    (cond
      [(null? s) #t]
      [else (odd-layers? (cdr s))])))

(define odd-layers?
  (lambda (s)
    (cond
      [(null? s) #f]
      [else (even-layers? (cdr s))])))

(define cons-cell-count
  (lambda (s)
    (cond
      [(null? s) 0]
      [(symbol? s) 0]
      [(number? s) 0]
      [else (+ (cons-cell-count (car s)) (add1 (cons-cell-count (cdr s))))])))

; a better way to do cons-cell-count
;;(define cons-cell-count
;;  (lambda (ls)
;;    (cond     
;;      [(pair? ls) (add1 (+ (cons-cell-count (car ls)) (cons-cell-count (cdr ls))))]
;;      [else 0])))

'((w . (x . ())) . (y . ((z .()) . ())))

(define fib-acc
  (lambda (x p1 p0)
    (cond
      [(eq? x 0) p0]
      [else (fib-acc (sub1 x) (+ p1 p0) p1)])))
