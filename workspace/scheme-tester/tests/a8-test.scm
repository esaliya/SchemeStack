(load "pmatch.scm")
(define *n*)
(define *m*)
(define *k*)
(define *v*)

(define ack
  (lambda () ; remember we had n m k
    (cond
      [(zero? *n*) (begin
                     (set! *k* *k*)
                     (set! *v* (add1 *m*))
                     (apply-k))]
      [(zero? *m*) (begin
                     (set! *k* *k*)
                     (set! *n* (sub1 *n*))
                     (set! *m* 1)
                     (ack))]
      [else (begin
              (set! *k* (ack-k *n* *k*))
              (set! *n* *n*)
              (set! *m* (sub1 *m*))
              (ack))])))

(define mt-k
  (lambda ()
    `(mt-k)))

(define ack-k
  (lambda (n k)
    `(ack-k ,n ,k)))

(define apply-k
  (lambda () ; remember we had k v
    (pmatch *k*
      [(mt-k) *v*]
      [(ack-k ,n ,k) (begin
                       (set! *k* k)
                       (set! *n* (sub1 n))
                       (set! *m* *v*)
                       (ack))])))

(define ack-driver
  (lambda (n m)
    (begin
      (set! *k* (mt-k))
      (set! *n* n)
      (set! *m* m)
      (ack))))
  