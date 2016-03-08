(define-syntax ==
  (syntax-rules ()
    ((_ u v)
     (lambda (s sk fk)
       (cond
         ((unify u v s) => (lambda (s^) (sk s^ fk)))
         (else (fk)))))))

(define take
  (lambda (n th)
    (cond
      ((or (null? th) (and n (zero? n))) '())
      (else (cons (car th) (take (and n (- n 1)) ((cdr th))))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (q) g g* ...)
     (let ((q (var 'q)))
       (let ((sk (lambda (s fk) `(,(reify q s) . ,fk)))
             (fk (lambda () '())))
         (if (and n (zero? n)) '()
             (take n ((conde (g g* ...)) empty-s sk fk))))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (q) g g* ...)
     (run #f (q) g g* ...))))

(define var? (lambda (x) (vector? x)))
(define var (lambda (x) (vector x)))
(define empty-s '())
(define ext-s (lambda (x v s) (cons `(,x . ,v) s)))

(define walk
  (lambda (v s)
    (cond
      ((var? v)
       (let ((a (assq v s)))
         (cond
           (a (walk (cdr a) s))
           (else v))))
      (else v))))

(define unify
  (lambda (v w s)
    (let ((v (walk v s)) (w (walk w s)))
      (cond
        ((eq? v w) s)
        ((var? v) (ext-s v w s))
        ((var? w) (ext-s w v s))
        ((and (pair? v) (pair? w))
         (let ((s (unify (car v) (car w) s)))
           (and s (unify (cdr v) (cdr w) s))))
        ((equal? v w) s)
        (else #f)))))

(define reify
  (lambda (t s)
    (let ((t (walk* t s)))
      (let ((s (reify-vars t)))
        (walk* t s)))))

(define walk*
  (lambda (t s)
    (let ((t (walk t s)))
      (if (pair? t)
        (cons
          (walk* (car t) s)
          (walk* (cdr t) s))
        t))))

(define reify-vars
  (lambda (t)
    (let rec ((t t) (s '()))
      (cond
        ((and (var? t) (not (assq t s)))
         (cons (cons t (reify-name (length s))) s))
        ((pair? t) (rec (cdr t) (rec (car t) s)))
        (else s)))))

(define reify-name
  (lambda (n) (string->symbol (string-append "_." (number->string n)))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g)) (lambda (s sk fk) (g s sk fk)))
    ((_ (g1 g* ...))
     (lambda (s sk fk)
       (g1 s (lambda (s^ fk^)
               ((conde (g* ...)) s^ sk fk^))
         fk)))
    ((_ (g1 g* ...) (g2 g^ ...) ...)
     (lambda (s sk fk)
       ((conde (g1 g* ...)) s sk
        (lambda ()
          ((conde (g2 g^ ...) ...) s sk fk)))))))
