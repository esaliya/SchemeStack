(define add
  (lambda (n)
    (if (eq? n 0)
        0
        (+ n (add (sub1 n))))))

(define add-cps
  (lambda (n k)
    (if (eq? n 0)
        (k 0)
        (add-cps (sub1 n) (lambda (v) (k (+ n v)))))))

(define empty-k
  (lambda ()
    (lambda (x) x)))


(define add-cc
  (lambda (n k)
    (if (eq? n 0)
        (k 0)
        (k (+ n (call/cc (lambda (c) (add-cc (sub1 n) c))))))))
           