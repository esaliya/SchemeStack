(define fac
  (lambda (n)
    (cond
      [(zero? n) 1]
      [else (* n (fac (sub1 n)))])))

(define faco
  (lambda (n out)
    (conde
      [(== 0 n) (== out 1)]
      [