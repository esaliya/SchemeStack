(define successor
  (lambda (n)
    `(lambda (f)
      (lambda (x)
;;        (f ((n f) x))
        (f ((,n f) x))
        ))))

(define encode
  (lambda (N)
;;    (if (= N 0) (lambda (f) (lambda (x) x)) (successor (encode (sub1 N))))
    (if (= N 0) '(lambda (f) (lambda (x) x)) (successor (encode (sub1 N))))
    ))

(define decode
  (lambda (n)
    ((n add1) 0)))
