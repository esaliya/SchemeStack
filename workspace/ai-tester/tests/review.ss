(define countdown
  (lambda (x)
    (if (< x 0)
        '()
        (cons x (countdown (sub1 x))))))

(define zip
  (lambda (l s)
    (if (null? l)
        '()
        (cons (cons (car l) (cons (car s) '())) (zip (cdr l) (cdr s)))))) 


;;(define f
;;  (lambda (x)
;;    (+ x 1)))

;;(f 2)

;;((lambda (x) (+ x 1)) 2)

;;(let ([x 2] [y 3] [g (lambda () (- x 1))])
;;  (g))

;;(letrec ([x 2] [g (+ x 1)])
;;  (g))

