(define walk-symbol
  (lambda (x original-list)
    (letrec ([walk (lambda (x al)
                             (cond
                               [(null? al) x]
                               [(eq? (caar al) x) (cond
                                                    [(symbol? (cdar al)) (walk (cdar al) original-list)]
                                                    [else (cdar al)])]
                               [else (walk x (cdr al))]))])
      (walk x original-list))))

(define remove
  (lambda (x s)                                                  
    (cond 
      [(null? s) '()]
      [(eq? (car s) x) (remove x (cdr s))]
      [else (cons (car s) (remove x (cdr s)))])))

(define append-remove-common ; should have called union :) 12/9/9
  (lambda (s1 s2)
    (cond
      [(null? s1) s2]
      [else (cons (car s1) (append-remove-common (cdr s1) (remove (car s1) s2)))])))

(define free
  (lambda (e)
      (pmatch e
        [,x (guard (symbol? x)) (list x)]
        [(lambda (,x) ,body) (remove x (free body))]
        [(,rator ,rand) (append-remove-common (free rator) (free rand))])))

(define bound
  (lambda (e)
    (pmatch e
      [,x (guard (symbol? x)) '()]
      [(lambda (,x) ,body) (let ([s (bound body)])
                             (cond
                               [(memq x (free body)) (cons x s)]
                               [else s]))]
      [(,rator ,rand) (append-remove-common (bound rator) (bound rand))])))

(define var-min
  (lambda (s)
    (num-occurs 'lambda s)))

(define replace  
  (lambda (s x m)
    (cond
      [(null? s) '()]
      [(equal? (car s) 'free-var) (cond
                                    [(eq? (cadr s) x) (list 'var m)]
                                    [else (cons (car s) (cdr s))])]  
      [(list? (car s)) (append (list (replace (car s) x m)) (replace (cdr s) x m))]
      [else (append (list (car s)) (replace (cdr s) x m))])))


(define num-occurs
  (lambda (x s)
    (cond
      [(null? s) 0]
      [(equal? (car s) x) (+ 1 (num-occurs x (cdr s)))]
      [(list? (car s)) (+ (num-occurs x (car s)) (num-occurs x (cdr s)))]
      [else (num-occurs x (cdr s))])))

(define lex
  (lambda (e)
    (pmatch e
      [,x (guard (symbol? x)) `(free-var ,x)]
      [(lambda (,x) ,body) `(lambda ,(let ([body-str (lex body)])
                                       (let ([m (var-min body-str)])
                                         (replace body-str x m))))]
      [(,rator ,rand) `(,(lex rator) ,(lex rand))])))

(define weird?
  (lambda (x e)
    (pmatch e
      [,x (guard (symbol? x)) #f]
      [(lambda (,x) ,body) (cond
                             [(and (memq x (free body)) (memq x (bound body))) #t]
                             [else (weird? x body)])]
      [(,rator ,rand) (or (weird? x rator) (weird? x rand))])))