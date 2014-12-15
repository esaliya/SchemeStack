;; Tests from a12
(define invalid-tests
  `(7
    #(1 2 3 4)
    (begin (nop) '3)
    (begin (void) 3)
    (if (true) '3 '4)
    (if (false) '3 '4)
    (letrec () (locals () '7))
    (letrec () (let ([x.1 '7]) (+ x.1 y.2)))
    (letrec () 
      (let ([x.1 '5] [box.1 (cons '1 '2)])
        (begin
          (set-cdr! box.1 (let ([y.2 '7]) y.2))
          (+ x.1 y.2))))
    (letrec () (let ([x.1 5]) x.1))
    (letrec () (let ([x.1 '5]) (begin (set! x.1 '7) x.1)))
    (letrec () (let ([x.1 #(1 2 3)]) x.1))
    (letrec () (let ([x.1 '#(1 2 3)]) x.1))
    (letrec () (let ([x.1 (cons '1 '2)]) (set-cdr! x.1 5)))
    (letrec () (let ([x.1 (make-vector '5)]) (vector-set! x.1 0 10)))
    (letrec () 7)
    (letrec () '5.5)
    (letrec () '#\a)
    (letrec () (let ([x '5]) x))
    (letrec () (if (if (= '0 '8) #t (= '1 '4)) '8 '6))
    (letrec ([vector-3?.0 (lambda (v.1)
                            (if (= (vector-length v.1) 3) '#t '#f))])
      (let ([v.2 (make-vector '3)])
        (begin
          (vector-set! v.2 '0 '5)
          (vector-set! v.2 '1 '10)
          (vecotr-set! v.2 '2 '20)
          (if (vector-3?.0 v.2)
              (+ (+ (vector-ref v.2 '0) (vector-ref v.2 '1))
                 (vector-ref v.2 '2))
              '#f))))
    (letrec ([vector-3?$0 (lambda (v.1)
                            (if (= (vector-length v.1) 3) '#t '#f))])
      (let ([v.2 (make-vector '3)])
        (begin
          (vector-set! v.2 '0 '5)
          (vector-set! v.2 '1 '10)
          (vector-set! v.2 '2 '20)
          (if (let ([test.3 (vector-3?$0 v.2)]) (= '#t test.3))
              (+ (+ (vector-ref v.2 '0) (vector-ref v.2 '1))
                 (vector-ref v.2 '2))
              '#f))))
    (letrec ([new-point$0 (lambda (x.1 y.2)
                            (let ([v.3 (make-vector '2)])
                              (begin
                                (vector-set! v.3 '0 x.1)
                                (vector-set! v.3 '1 x.1)
                                v.3)))]
             [new-3d-point$0 (lambda (x.4 y.5 z.6)
                               (let ([v.7 (make-vector '3)])
                                 (begin
                                   (vector-set! v.7 '0 x.4)
                                   (vector-set! v.7 '1 y.5)
                                   (vector-set! v.7 '2 z.6)
                                   v.7)))])
      (let ([pt1.8 (new-point$0 '1 '2)] [pt2.9 (new-3d-point$0 '1 '2 '3)])
        (+ (vector-ref pt1.8 '0) (vector-ref pt2.9 '0))))
    (letrec ([foo$0 (lambda (x.1)
                      (let ([x.1 x.1])
                        (+ x.1 x.1)))])
      (foo$0 '5))
    (letrec ()
      (let ([x.1 '(1 2 3)])
        x.1))
    (letrec () 'a)
    (letrec ([bar (lambda () (let ([a.1 5]) a.1))]) (bar))
    (letrec ([foo$0 (lambda (x.1 y.2) (+ x.1 y.2))]) (bar$1))
    (letrec () '1152921504606846976)
    (letrec () '-1152921504606846977)
    (letrec () (sra '5 '6))
    (letrec () (logand '5 '2))
    (letrec () (logor '7 '8))
    (letrec () x.1)
    (letrec () (let ([x.1 (alloc '8)])
                 (begin
                   (mset! x.1 '0 '10)
                   (mref x.1 '0))))
    (letrec ([f$1 (lambda (x.3) (let ([x.4 x.3]) x.4))]
             [g$2 (lambda (y.4) y.4)])
      (let ([z.5 '17]) (f$1 (g$2 z.5))))
    (letrec ([f$1 (lambda (x.3) x.3)]
             [g$2 (lambda (y.4) y.4)])
      (let ([z.4 '17]) (f$1 (g$2 z.4))))
    (letrec ([f.1 (lambda (x.3) x.3)]
             [g.2 (lambda (y.3) y.3)])
      (f.1 (g.2 '17)))
    (letrec ()
      (let ([x.1 '15])
        (+ x.1 rax)))
    (letrec () 
      (let ([v.1 (make-vector '10)])
        (let ([v.2 (make-vector (vector-set! v.1 '15))])
          v.2)))
    (letrec ()
      (let ([x.1 (cons '1 '2)] [y.2 (cons '3 '4)])
        (if (pair? x.1 y.2) (+ (car x.1) (car y.2)) x.1)))
    ;; wrong number of args -- nullary with argument
    (letrec () (void '1))
    ;; wrong number of args -- 0 for 1
    (letrec () (car))
    (letrec () (cdr))
    (letrec () (make-vector))
    (letrec () (vector-length))
    (letrec () (boolean?))
    (letrec () (fixnum?))
    (letrec () (null?))
    (letrec () (pair?))
    (letrec () (vector?))
    ;; wrong number of args -- 2 for 1
    (letrec () (let ([x.1 (cons '1 '2)]) (car x.1 (cons '3 '4))))
    (letrec () (let ([x.1 (cons '1 '2)] [y.2 (cons '3 '4)])
                 (cdr x.1 y.2)))
    (letrec () (make-vector '5 '6))
    (letrec () (vector-length (make-vector '7) '1))
    (letrec () (boolean? '#t '#f))
    (letrec () (fixnum? '7 '8))
    (letrec () (null? '() '()))
    (letrec () (pair? (cons '1 '2) (cons '3 '4)))
    (letrec () (vector? (make-vector '1) (make-vector '2)))
    ;; wrong number of args -- 1 for 2
    (letrec () (* '1))
    (letrec () (+ '2))
    (letrec () (- '3))
    (letrec () (cons '4))
    (letrec () (vector-ref (make-vector '5)))
    (letrec () (< '6))
    (letrec () (<= '7))
    (letrec () (= '8))
    (letrec () (>= '9))
    (letrec () (> '10))
    (letrec () (eq? '11))
    (letrec () (let ([x.1 (cons (void) (void))])
                 (begin
                   (set-car! x.1)
                   x.1)))
    (letrec () (let ([x.1 (cons (void) (void))])
                 (begin
                   (set-car! x.1)
                   x.1)))
    ;; wrong number of args -- 3 for 2
    (letrec () (* '1 '2 '3))
    (letrec () (+ '2 '3 '4))
    (letrec () (- '3 '5 '6))
    (letrec () (cons '4 '5 '6))
    (letrec () (vector-ref (make-vector '5) '0 '10))
    (letrec () (< '6 '7 '8))
    (letrec () (<= '7 '8 '9))
    (letrec () (= '8 '9 '10))
    (letrec () (>= '9 '10 '11))
    (letrec () (> '10 '11 '12))
    (letrec () (eq? '11 '12 '13))
    (letrec () (let ([x.1 (cons (void) (void))])
                 (begin
                   (set-car! x.1 '0 '1)
                   x.1)))
    (letrec () (let ([x.1 (cons (void) (void))])
                 (begin
                   (set-car! x.1 '2 '3)
                   x.1)))
    ;; wrong number of args -- 2 for 3
    (letrec () (let ([x.1 (make-vector '2)])
                 (begin
                   (vector-set! x.1 '0)
                   x.1)))
    ;; wrong number of args -- 4 for 3
    (letrec () (let ([x.1 (make-vector '2)])
                 (begin
                   (vector-set! x.1 '0 '3 '1)
                   x.1)))
    ))

(define tests 
  '('7
    (begin '7)
    (letrec () '7)
    (letrec () (letrec () '7))
    (let ([x.1 (cons '1 '2)]) (pair? x.1))
    (let ([x.1 '5] [y.2 '10])
      (begin
        (+ x.1 y.2)
        x.1))
    (let ([tf.1 (cons '#t '#f)])
      (if (car tf.1) '5 '10))
    (let ([tf.1 (cons '#t '#f)])
      (if (cdr tf.1) '5 '10))
    (let ([x.1 '3])
      (letrec ([f.2 (lambda () x.1)])
        (f.2)))
    (cdr (let ([x.1 (cons '1 '2)])
           (begin
             (set-car! x.1 '10)
             (set-cdr! x.1 '20)
             x.1)))
    (let ([x.1 (cons '1 '2)])
      (set-car! x.1 '4))
    (+ (let ([x.1 '3])
         (letrec ([f.2 (lambda (y.3) (+ x.1 y.3))])
           (f.2 '5)))
       '7)
    (letrec ([even?.1 (lambda (x.3) (if (= x.3 '0) '#t (odd?.2 (- x.3 '1))))]
             [odd?.2 (lambda (x.4) (if (even?.1 x.4) '#f '#t))])
      (cons (even?.1 '17) (odd?.2 '17)))
    (letrec ([mult.2 (lambda (n.4)
                       (letrec ([anon.6 (lambda (m.5) (* n.4 m.5))])
                         anon.6))]
             [succ.1 (lambda (n.3) (+ n.3 '1))])
      (- (* '4 '5) ((mult.2 (succ.1 '3)) (succ.1 '4))))

    (letrec ([f.1 (lambda () f.1)]) (procedure? (f.1)))
    (letrec ([vectors?.0 (lambda (v.1 v.2)
                           (if (vector? v.1)
                               (vector? v.2)
                               '#f))])
      (let ([v.3 (make-vector '2)] [v.4 (make-vector '2)])
        (begin
          (vector-set! v.3 '0 '10)
          (vector-set! v.3 '1 '20)
          (vector-set! v.4 '0 '5)
          (vector-set! v.4 '1 '15)
          (if (eq? (vectors?.0 v.3 v.4) '#t)
              (+
                (* (vector-ref v.3 '0) (vector-ref v.4 '0))
                (* (vector-ref v.3 '1) (vector-ref v.4 '1)))
              '100))))
    (let ([x.1 (cons '5 '10)])
      (let ([z.2 (void)])
        (if (set-car! x.1 '5)
            z.2
            (+ '5 '3))))
    (let ([a.1 (cons '5 '10)])
      (let ([is-pair.2 (pair? a.1)])
        (if is-pair.2 (car a.1) a.1)))
    (let ([a.1 (cons '5 '10)])
      (let ([is-pair.2 (if (pair? a.1) '#t '#f)])
        (if is-pair.2 (car a.1) a.1)))
    (let ([x.1 '5] [y.2 '7])
      (if (if (= x.1 y.2) (void) (= (+ x.1 '2) y.2)) '172 '63))
    ;; value primitives in effect context
    (let ([x.1 '5]) (begin (* '3 x.1) x.1))
    (let ([x.1 '5]) (begin (+ '3 x.1) x.1))
    (let ([x.1 '5]) (begin (- '3 x.1) x.1))
    (let ([x.1 (cons '1 '5)]) (begin (car x.1) x.1))
    (let ([x.1 (cons '1 '5)]) (begin (cdr x.1) x.1))
    (letrec () (let ([x.1 '1] [y.2 '5]) (begin (cons x.1 y.2) x.1)))
    (letrec () (begin (make-vector '5) '7))
    (letrec () (let ([v.1 (make-vector '2)])
                 (begin (vector-length v.1) '7)))
    (letrec () (let ([v.1 (make-vector '2)])
                 (begin (vector-ref v.1 '0) '7)))
    (letrec () (begin (void) '5))
    ;; value primitives in pred
    (letrec () (if (+ '3 '5) '7 '8))
    (letrec () (if (* '3 '5) '7 '8))
    (letrec () (if (- '3 '5) '7 '8))
    (letrec () (if (cons '3 '5) '7 '8))
    (if (car (cons '#t '#f)) '7 '8)
    (if (cdr (cons '#t '#f)) '7 '8)
    (letrec () (if (make-vector '10) '7 '8))
    (letrec () 
      (let ([v.1 (make-vector '10)])
        (if (vector-length v.1) '7 '8)))
    (letrec () 
      (let ([v.1 (make-vector '10)])
        (begin
          (vector-set! v.1 '0 '#t)
          (if (vector-ref v.1 '0) '7 '8))))
    (letrec () (if (void) '7 '8))
    ;; pred prims in value
    (letrec () (< '7 '8))
    (letrec () (<= '7 '8))
    (= '7 '8)
    (letrec () (>= '7 '8))
    (> '7 '8)
    (letrec () (boolean? '#f))
    (letrec () 
      (let ([x.1 (cons '1 '())] [y.2 (cons '1 '())])
        (eq? x.1 y.2)))
    (letrec () (fixnum? '7))
    (null? '())
    (letrec () (pair? (cons '1 '())))
    (vector? (make-vector '1))
    ;; pred prims in effect
    (letrec () (begin (< '7 '8) '7))
    (begin (<= '7 '8) '7)
    (letrec () (begin (= '7 '8) '7))
    (begin (>= '7 '8) '7)
    (letrec () (begin (> '7 '8) '8))
    (letrec () (begin (boolean? '#f) '9))
    (letrec () 
      (let ([x.1 (cons '1 '())] [y.2 (cons '1 '())])
        (begin (eq? x.1 y.2) '10)))
    (letrec () (begin (fixnum? '7) '10))
    (letrec () (begin (null? '()) '15))
    (letrec () (begin (pair? (cons '1 '())) '20))
    (letrec () (begin (vector? (make-vector '1)) '10))
    ;; effect prims in value
    (letrec () (set-car! (cons '1 '2) '10))
    (letrec () (set-cdr! (cons '1 '2) '14))
    (letrec () (vector-set! (make-vector '4) '0 '10))
    ;; effect prims in pred
    (if (set-car! (cons '1 '2) '10) '7 '8)
    (letrec () (if (set-cdr! (cons '1 '2) '14) '9 '10))
    (letrec () (if (vector-set! (make-vector '4) '0 '10) '11 '12))
    (letrec () '#f)
    '#t
    (letrec () '())
    (letrec () (* '5 '7))
    (+ '5 '7)
    (letrec () (- '5 '7))
    (letrec () (cons '#f '3))
    (letrec () (car (cons '#f '3)))
    (letrec () (cdr (cons '#f '3)))
    (letrec ()
      (let ([x.1 (cons '3 '())])
        (begin
          (set-car! x.1 '4)
          (set-cdr! x.1 (cons '5 '#f))
          x.1)))
    (letrec () (make-vector '0))
    (letrec () (vector-length (make-vector '0)))
    (let ([v.1 (make-vector '1)])
      (begin
        (vector-set! v.1 '0 '5)
        v.1))
    (let ([v.1 (make-vector '1)])
      (begin
        (vector-set! v.1 '0 '())
        (vector-ref v.1 '0)))
    (let ([v.1 (make-vector '2)])
      (begin
        (vector-set! v.1 '0 '5)
        (vector-set! v.1 '1 '7)
        (- (vector-ref v.1 '0) (vector-ref v.1 '1))))
    (let ([n.1 '2] [i.2 '0] [j.3 '1])
      (let ([v.4 (make-vector n.1)])
       (begin
         (vector-set! v.4 i.2 '5)
         (vector-set! v.4 j.3 '7)
         (- (vector-ref v.4 i.2) (vector-ref v.4 j.3)))))
    (letrec () (void))

    (let ([n.1 '19]) (if (<= n.1 '19) '#t '#f))
    (let ([n.1 '19]) (if (>= n.1 '19) '#t '#f))
    (let ([n.1 '19]) (if (= n.1 '19) '#t '#f))
    (let ([n.1 '19]) (if (< n.1 '19) '#t '#f))
    (let ([n.1 '19]) (if (> n.1 '19) '#t '#f))
    (let ([n.1 '20]) (if (<= n.1 '19) '#t '#f))
    (let ([n.1 '20]) (if (>= n.1 '19) '#t '#f))
    (let ([n.1 '20]) (if (= n.1 '19) '#t '#f))
    (let ([n.1 '20]) (if (< n.1 '19) '#t '#f))
    (let ([n.1 '20]) (if (> n.1 '19) '#t '#f))
    (let ([n.1 '17]) (if (<= n.1 '19) '#t '#f))
    (let ([n.1 '17]) (if (>= n.1 '19) '#t '#f))
    (let ([n.1 '17]) (if (= n.1 '19) '#t '#f))
    (let ([n.1 '17]) (if (< n.1 '19) '#t '#f))
    (let ([n.1 '17]) (if (> n.1 '19) '#t '#f))

    (let ([n.1 '#f]) (if (eq? n.1 n.1) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 '#f) '() '-1))
    (let ([n.1 '#t]) (if (eq? n.1 '#f) '() '-1))
    (let ([n.1 '17]) (if (eq? n.1 '#f) '() '-1))
    (let ([n.1 '-17]) (if (eq? n.1 '#f) '() '-1))
    (let ([n.1 '()]) (if (eq? n.1 '#f) '() '-1))
    (let ([n.1 (cons '1 '2)]) (if (eq? n.1 '#f) '() '-1))
    (let ([n.1 (make-vector '3)]) (if (eq? n.1 '#f) '() '-1))
    (let ([n.1 (void)]) (if (eq? n.1 '#f) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 n.1) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 '#t) '() '-1))
    (let ([n.1 '#t]) (if (eq? n.1 '#t) '() '-1))
    (let ([n.1 '17]) (if (eq? n.1 '#t) '() '-1))
    (let ([n.1 '-17]) (if (eq? n.1 '#t) '() '-1))
    (let ([n.1 '()]) (if (eq? n.1 '#t) '() '-1))
    (let ([n.1 (cons '1 '2)]) (if (eq? n.1 '#t) '() '-1))
    (let ([n.1 (make-vector '3)]) (if (eq? n.1 '#t) '() '-1))
    (let ([n.1 (void)]) (if (eq? n.1 '#t) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 n.1) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 '()) '() '-1))
    (let ([n.1 '#t]) (if (eq? n.1 '()) '() '-1))
    (let ([n.1 '17]) (if (eq? n.1 '()) '() '-1))
    (let ([n.1 '-17]) (if (eq? n.1 '()) '() '-1))
    (let ([n.1 '()]) (if (eq? n.1 '()) '() '-1))
    (let ([n.1 (cons '1 '2)]) (if (eq? n.1 '()) '() '-1))
    (let ([n.1 (make-vector '3)]) (if (eq? n.1 '()) '() '-1))
    (let ([n.1 (void)]) (if (eq? n.1 '()) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 n.1) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 '17) '() '-1))
    (let ([n.1 '#t]) (if (eq? n.1 '17) '() '-1))
    (let ([n.1 '17]) (if (eq? n.1 '17) '() '-1))
    (let ([n.1 '-17]) (if (eq? n.1 '17) '() '-1))
    (let ([n.1 '()]) (if (eq? n.1 '17) '() '-1))
    (let ([n.1 (cons '1 '2)]) (if (eq? n.1 '17) '() '-1))
    (let ([n.1 (make-vector '3)]) (if (eq? n.1 '17) '() '-1))
    (let ([n.1 (void)]) (if (eq? n.1 '17) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 n.1) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 (cons '1 '2)) '() '-1))
    (let ([n.1 '#t]) (if (eq? n.1 (cons '1 '2)) '() '-1))
    (let ([n.1 '17]) (if (eq? n.1 (cons '1 '2)) '() '-1))
    (let ([n.1 '-17]) (if (eq? n.1 (cons '1 '2)) '() '-1))
    (let ([n.1 '()]) (if (eq? n.1 (cons '1 '2)) '() '-1))
    (let ([n.1 (cons '1 '2)]) (if (eq? n.1 (cons '1 '2)) '() '-1))
    (let ([n.1 (make-vector '3)]) (if (eq? n.1 (cons '1 '2)) '() '-1))
    (let ([n.1 (void)]) (if (eq? n.1 (cons '1 '2)) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 n.1) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 (make-vector '3)) '() '-1))
    (let ([n.1 '#t]) (if (eq? n.1 (make-vector '3)) '() '-1))
    (let ([n.1 '17]) (if (eq? n.1 (make-vector '3)) '() '-1))
    (let ([n.1 '-17]) (if (eq? n.1 (make-vector '3)) '() '-1))
    (let ([n.1 '()]) (if (eq? n.1 (make-vector '3)) '() '-1))
    (let ([n.1 (cons '1 '2)]) (if (eq? n.1 (make-vector '3)) '() '-1))
    (let ([n.1 (make-vector '3)]) (if (eq? n.1 (make-vector '3)) '() '-1))
    (let ([n.1 (void)]) (if (eq? n.1 (make-vector '3)) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 n.1) '() '-1))
    (let ([n.1 '#f]) (if (eq? n.1 (void)) '() '-1))
    (let ([n.1 '#t]) (if (eq? n.1 (void)) '() '-1))
    (let ([n.1 '17]) (if (eq? n.1 (void)) '() '-1))
    (let ([n.1 '-17]) (if (eq? n.1 (void)) '() '-1))
    (let ([n.1 '()]) (if (eq? n.1 (void)) '() '-1))
    (let ([n.1 (cons '1 '2)]) (if (eq? n.1 (void)) '() '-1))
    (let ([n.1 (make-vector '3)]) (if (eq? n.1 (void)) '() '-1))
    (let ([n.1 (void)]) (if (eq? n.1 (void)) '() '-1))

    (let ([n.1 '#f]) (if (boolean? n.1) '5 '-7))
    (let ([n.1 '#t]) (if (boolean? n.1) '5 '-7))
    (let ([n.1 '17]) (if (boolean? n.1) '5 '-7))
    (let ([n.1 '()]) (if (boolean? n.1) '5 '-7))
    (let ([n.1 (cons '1 '2)]) (if (boolean? n.1) '5 '-7))
    (let ([n.1 (make-vector '3)]) (if (boolean? n.1) '5 '-7))
    (let ([n.1 (void)]) (if (boolean? n.1) '5 '-7))
    (let ([n.1 '#f]) (if (fixnum? n.1) '5 '-7))
    (let ([n.1 '#t]) (if (fixnum? n.1) '5 '-7))
    (let ([n.1 '17]) (if (fixnum? n.1) '5 '-7))
    (let ([n.1 '()]) (if (fixnum? n.1) '5 '-7))
    (let ([n.1 (cons '1 '2)]) (if (fixnum? n.1) '5 '-7))
    (let ([n.1 (make-vector '3)]) (if (fixnum? n.1) '5 '-7))
    (let ([n.1 (void)]) (if (fixnum? n.1) '5 '-7))
    (let ([n.1 '#f]) (if (null? n.1) '5 '-7))
    (let ([n.1 '#t]) (if (null? n.1) '5 '-7))
    (let ([n.1 '17]) (if (null? n.1) '5 '-7))
    (let ([n.1 '()]) (if (null? n.1) '5 '-7))
    (let ([n.1 (cons '1 '2)]) (if (null? n.1) '5 '-7))
    (let ([n.1 (make-vector '3)]) (if (null? n.1) '5 '-7))
    (let ([n.1 (void)]) (if (null? n.1) '5 '-7))
    (let ([n.1 '#f]) (if (pair? n.1) '5 '-7))
    (let ([n.1 '#t]) (if (pair? n.1) '5 '-7))
    (let ([n.1 '17]) (if (pair? n.1) '5 '-7))
    (let ([n.1 '()]) (if (pair? n.1) '5 '-7))
    (let ([n.1 (cons '1 '2)]) (if (pair? n.1) '5 '-7))
    (let ([n.1 (make-vector '3)]) (if (pair? n.1) '5 '-7))
    (let ([n.1 (void)]) (if (pair? n.1) '5 '-7))
    (let ([n.1 '#f]) (if (vector? n.1) '5 '-7))
    (let ([n.1 '#t]) (if (vector? n.1) '5 '-7))
    (let ([n.1 '17]) (if (vector? n.1) '5 '-7))
    (let ([n.1 '()]) (if (vector? n.1) '5 '-7))
    (let ([n.1 (cons '1 '2)]) (if (vector? n.1) '5 '-7))
    (let ([n.1 (make-vector '3)]) (if (vector? n.1) '5 '-7))
    (let ([n.1 (void)]) (if (vector? n.1) '5 '-7))

    (+ (let ([x.1 '7] [y.2 '2])
         (if (if (= x.1 '7) (< y.2 '0) (<= '0 y.2)) '77 '88))
       '99)
    (+ (let ([x.1 '7] [y.2 '-22])
         (if (if (= x.1 '7) (< y.2 '0) (<= '0 y.2)) '77 '88))
       '99)
    (+ (let ([x.1 '8] [y.2 '2])
         (if (if (= x.1 '7) (< y.2 '0) (<= '0 y.2)) '77 '88))
       '99)
    (+ (let ([x.1 '8] [y.2 '-22])
         (if (if (= x.1 '7) (< y.2 '0) (<= '0 y.2)) '77 '88))
       '99)

    (if (= (+ '7 (* '2 '4)) (- '20 (+ (+ '1 '1) (+ (+ '1 '1) '1))))
        (+ '1 (+ '1 (+ '1 (+ '1 (+ '1 '10)))))
        '0)
    (let ([a.1 '10])
      (let ([b.2 (if (< '7 a.1) a.1 (+ a.1 a.1))])
        b.2))
    (let ([a.1 '5])
      (let ([b.2 (if (< '7 a.1) a.1 (+ a.1 a.1))])
        b.2))
    (let ([c.1 '10] [a.2 '5])
      (if (< a.2 c.1) a.2 c.1))
    (let ([a.1 '5])
      (let ([b.2 (if (< a.1 '10) (+ a.1 a.1) a.1)])
        b.2))
    (letrec ([f.0 (lambda (x.1) (+ '1 x.1))])
      (f.0 (let ([f.2 '3]) (+ f.2 '1))))
    ((letrec ([f.0 (lambda (x.1) (+ '1 x.1))]) f.0)
     (let ([f.2 '3]) (+ f.2 '1)))
    (cons (letrec ([f.0 (lambda (h.1 v.2) (* h.1 v.2))])
            (letrec ([k.7 (lambda (x.3) (+ x.3 '5))])
              (let ([x.5 '15])
                (letrec ([g.8 (lambda (x.4) (+ '1 x.4))])
                  (k.7 (g.8 (let ([g.6 '3]) (f.0 g.6 x.5))))))))
          '())
    (letrec () (+ (let ((x.1 '3)) x.1) '3))
    (letrec () (begin (let ((x.1 '3)) (void)) '4))
    (letrec () (if (let ((x.1 '3)) (= x.1 '4)) '5 '6))
    (letrec () (begin (if (let ((x.1 '3)) (= x.1 '4)) (void) (void)) '8))
    (letrec () (+ (if (begin (void) (let ((x.1 '3)) (= x.1 '4))) '3 '4) '5))
    (letrec ([one.0 (lambda (n.1) 
                      (if (= '0 n.1) '1 (one.0 (- n.1 '1))))])
       (one.0 '13))
    (letrec ([f.0 (lambda (p.2) (- (cdr p.2) (car p.2)))])
      (f.0 (cons '73 '35)))
    (letrec ([f.0 (lambda (p.2 i.3 i.4) (- (vector-ref p.2 i.3) (vector-ref p.2 i.4)))])
      (let ([x.1 (make-vector '2)])
        (begin
          (vector-set! x.1 '0 '73)
          (vector-set! x.1 '1 '35)
          (+ (f.0 x.1 '0 '1) '-41))))
    (letrec ([f.0 (lambda (p.3)
                    (- (vector-ref
                         (vector-ref (vector-ref (vector-ref (vector-ref p.3 '0) '0) '1) '0)
                         (vector-ref (vector-ref p.3 '1) (vector-ref (vector-ref p.3 '0) '4)))
                       (vector-ref
                         (vector-ref p.3 (vector-ref p.3 '2))
                         (vector-ref (vector-ref p.3 '0) (vector-ref p.3 '4)))))])
      (let ([x.1 (make-vector '6)] [x.2 (make-vector '7)])
        (begin
          (vector-set! x.1 '0 x.2)
          (vector-set! x.1 '1 x.1)
          (vector-set! x.2 '0 x.1)
          (vector-set! x.2 '1 '-4421)
          (vector-set! x.1 '2 '0)
          (vector-set! x.1 '3 '-37131)
          (vector-set! x.1 '4 '4)
          (vector-set! x.1 '5 '6)
          (vector-set! x.2 '2 '-55151)
          (vector-set! x.2 '3 '-32000911)
          (vector-set! x.2 '4 '5)
          (vector-set! x.2 '5 '55)
          (vector-set! x.2 '6 '-36)
          (* (f.0 x.1) '2))))
    (letrec ([remq.1 (lambda (x.2 ls.3)
                       (if (null? ls.3)
                           '()
                           (if (eq? (car ls.3) x.2)
                               (remq.1 x.2 (cdr ls.3))
                               (cons (car ls.3) (remq.1 x.2 (cdr ls.3))))))])
      (remq.1 '3 (cons '3 (cons '1 (cons '3 '())))))
    (let ([n.5 '4])
      (let ([v.6 (make-vector n.5)])
        (letrec ([iota-fill!.1 (lambda (v.2 i.3 n.4)
                                 (if (= i.3 n.4)
                                     (void)
                                     (begin
                                       (vector-set! v.2 i.3 i.3)
                                       (iota-fill!.1 v.2 (+ i.3 '1) n.4))))])
          (begin
            (iota-fill!.1 v.6 '0 n.5)
            v.6))))
    (letrec ([vector-scale!.0 (lambda (vect.1 scale.2)
                                (let ([size.3 (vector-length vect.1)])
                                  (vector-scale!.12 size.3 vect.1 scale.2)))]
             [vector-scale!.12 (lambda (offset.4 vect.5 scale.6)
                                (if (< offset.4 '1)
                                    '0
                                    (begin
                                      (vector-set! vect.5 (- offset.4 '1)
                                        (* (vector-ref vect.5 (- offset.4 '1))
                                           scale.6))
                                      (vector-scale!.12 (- offset.4 '1) vect.5
                                        scale.6))))]
             [vector-sum.13 (lambda (vect.7)
                             (vector-sum.14 (vector-length vect.7) vect.7))]
             [vector-sum.14 (lambda (offset.9 vect.10)
                             (if (< offset.9 '1)
                                 '0
                                 (+ (vector-ref vect.10 (- offset.9 '1))
                                    (vector-sum.14 (- offset.9 '1) vect.10))))])
      (let ([vect.11 (make-vector '5)])
        (begin
          (vector-set! vect.11 '0 '123)
          (vector-set! vect.11 '1 '10)
          (vector-set! vect.11 '2 '7)
          (vector-set! vect.11 '3 '12)
          (vector-set! vect.11 '4 '57)
          (vector-scale!.0 vect.11 '10)
          (vector-sum.13 vect.11))))
    (let ([vect.11 (make-vector '5)])
      (begin
        (vector-set! vect.11 '0 '123)
        (vector-set! vect.11 '1 '10)
        (vector-set! vect.11 '2 '7)
        (vector-set! vect.11 '3 '12)
        (vector-set! vect.11 '4 '57)
        (letrec ([vector-scale!.0 (lambda (vect.1 scale.2)
                                    (let ([size.3 (vector-length vect.1)])
                                      (vector-scale!.12 size.3 vect.1 scale.2)))]
                 [vector-scale!.12 (lambda (offset.4 vect.5 scale.6)
                                    (if (< offset.4 '1)
                                        '0
                                        (begin
                                          (vector-set! vect.5 (- offset.4 '1)
                                            (* (vector-ref vect.5 (- offset.4 '1))
                                               scale.6))
                                          (vector-scale!.12 (- offset.4 '1) vect.5
                                            scale.6))))])
          (vector-scale!.0 vect.11 '10))
        (letrec ([vector-sum.13 (lambda (vect.7)
                                 (vector-sum.14 (vector-length vect.7) vect.7))]
                 [vector-sum.14 (lambda (offset.9 vect.10)
                                 (if (< offset.9 '1)
                                     '0
                                     (+ (vector-ref vect.10 (- offset.9 '1))
                                        (vector-sum.14 (- offset.9 '1) vect.10))))])
          (vector-sum.13 vect.11))))
    (letrec ([length.0 (lambda (ptr.6)
                         (if (null? ptr.6)
                             '0
                             (+ '1 (length.0 (cdr ptr.6)))))])
      (length.0 (cons '5 (cons '10 (cons '11 (cons '5 (cons '15 '())))))))
    ((letrec ([length.0 (lambda (ptr.6)
                          (if (null? ptr.6)
                              '0
                              (+ '1 (length.0 (cdr ptr.6)))))])
       length.0)
     (cons '5 (cons '10 (cons '11 (cons '5 (cons '15 '()))))))
    (letrec ([count-leaves.0 (lambda (ptr.6)
                               (if (pair? ptr.6)
                                   (+ (count-leaves.0 (car ptr.6))
                                      (count-leaves.0 (cdr ptr.6)))
                                   '1))])
      (count-leaves.0
        (cons 
          (cons
            '0
            (cons '0 '0))
          (cons
            (cons
              (cons (cons '0 (cons '0 '0)) '0)
              '0)
            (cons (cons (cons '0 '0) (cons '0 (cons '0 '0)))
                  (cons (cons '0 '0) '0))))))
    (letrec ([add1.3 (lambda (n.6) (+ n.6 '1))]
             [map.4 (lambda (f.7 ls.8)
                      (if (null? ls.8)
                          '()
                          (cons (f.7 (car ls.8)) 
                                (map.4 f.7 (cdr ls.8)))))]
             [sum.5 (lambda (ls.9)
                      (if (null? ls.9)
                          '0
                          (+ (car ls.9) (sum.5 (cdr ls.9)))))])
      (let ([ls.10 (cons '5 (cons '4 (cons '3 (cons '2 (cons '1 '())))))])
        (let ([ls.11 (cons '10 (cons '9 (cons '8 (cons '7 (cons '6 ls.10)))))])
          (sum.5 (map.4 add1.3 ls.11)))))
    (letrec ([list-ref.3 (lambda (ls.11 offset.12)
                           (if (= offset.12 '0)
                               (car ls.11)
                               (list-ref.3 (cdr ls.11) (- offset.12 '1))))]
             [add.6 (lambda (v.13 w.14) (+ v.13 w.14))]
             [sub.70 (lambda (v.15 w.16) (- v.15 w.16))]
             [mult.8 (lambda (v.17 w.18) (* v.17 w.18))]
             [expt.90 (lambda (v.217 w.218) 
                        (if (= w.218 '0)
                            '1
                            (* v.217 (expt.90 v.217 (- w.218 '1)))))]
             [selector.4 (lambda (op*.7 sel.19 rand1.20 rand2.21)
                           (if (null? sel.19)
                               '0
                               (cons ((list-ref.3 op*.7 (car sel.19))
                                      (car rand1.20) (car rand2.21))
                                     (selector.4 op*.7 (cdr sel.19)
                                                 (cdr rand1.20)
                                                 (cdr rand2.21)))))]
             [sum.5 (lambda (ls.9)
                      (if (pair? ls.9)
                          (+ (car ls.9) (sum.5 (cdr ls.9)))
                          '0))])
      (sum.5 (selector.4 
               (cons add.6 (cons sub.70 (cons mult.8 (cons expt.90 '()))))
               (cons '2 (cons '0 (cons '1 (cons '3 (cons '2 '())))))
               (cons '5 (cons '9 (cons '10 (cons '2 (cons '3 '())))))
               (cons '3 (cons '1 (cons '3 (cons '3 (cons '8 '()))))))))
    (letrec ([thunk-num.0 (lambda (n.1)
                            (let ([th.2 (make-vector '2)])
                              (begin 
                                (vector-set! th.2 '0 force-th.12)
                                (vector-set! th.2 '1 n.1)
                                th.2)))]
             [force-th.12 (lambda (cl.3)
                           (vector-ref cl.3 '1))]
             [add-ths.13 (lambda (cl1.4 cl2.5 cl3.6 cl4.7)
                          (+ (+ ((vector-ref cl1.4 '0) cl1.4)
                                ((vector-ref cl2.5 '0) cl2.5))
                             (+ ((vector-ref cl3.6 '0) cl3.6)
                                ((vector-ref cl4.7 '0) cl4.7))))])
      (add-ths.13 (thunk-num.0 '5) (thunk-num.0 '17) (thunk-num.0 '7)
                  (thunk-num.0 '9)))
    (let ([v1.13 (make-vector '5)] [p.20 (cons '() (void))])
      (begin
        (vector-set! v1.13 '0 '134)
        (vector-set! v1.13 '1 '123)
        (vector-set! v1.13 '2 '503)
        (vector-set! v1.13 '3 p.20)
        (vector-set! v1.13 '4 '255)
        (let ([v2.14 (make-vector '5)])
          (begin
            (vector-set! v2.14 '0 '134)
            (vector-set! v2.14 '1 '123)
            (vector-set! v2.14 '2 '503)
            (vector-set! v2.14 '3 p.20)
            (vector-set! v2.14 '4 '255)
            (letrec ([vector-equal?.3 (lambda (vect1.8 vect2.9)
                                        (let ([n.15 (vector-length vect1.8)])
                                          (if (= (vector-length vect2.9) n.15)
                                              (vector-equal?.4 vect1.8 vect2.9 (- n.15 '1))
                                              '0)))]
                     [vector-equal?.4 (lambda (vect1.11 vect2.12 off.10)
                                        (if (< off.10 '0)
                                            '#t
                                            (if (eq? (vector-ref vect1.11 off.10)
                                                     (vector-ref vect2.12 off.10))
                                                (vector-equal?.4 vect1.11 vect2.12 (- off.10 '1))
                                                '#f)))])
              (if (eq? (vector-equal?.3 v1.13 v2.14) '#f)
                  '-100
                  (if (eq? (begin
                             (vector-set! v2.14 '3 (cons '() (void)))
                             (vector-equal?.3 v1.13 v2.14))
                           '#f)
                      '200
                      '100)))))))
    (letrec ([div.400 (lambda (d.401 n.402) (div-help.500 d.401 n.402 '0))]
             [div-help.500 (lambda (d.501 n.502 q.503)
                             (if (> n.502 d.501)
                                 q.503
                                 (div-help.500 (- d.501 n.502) n.502 (+ q.503 '1))))])
      (letrec ([alloc.100 (lambda (n.101) (make-vector (div.400 n.101 '8)))]
               [mref.200 (lambda (x.201 y.202)
                           (if (vector? x.201)
                               (vector-ref x.201 (div.400 y.202 '8))
                               (vector-ref y.202 (div.400 x.201 '8))))]
               [mset!.300 (lambda (x.301 y.302 z.303)
                            (begin
                              (if (vector? x.301)
                                  (vector-set! x.301 (div.400 y.302 '8) z.303)
                                  (vector-set! y.302 (div.400 x.301 '8) z.303))
                              (void)))])
        (letrec ([stack-new.0 (lambda (size.1)
                                (let ([store.3 (alloc.100 (* '8 size.1))]
                                      [meths.4 (alloc.100 (* '3 '8))]
                                      [stack.2 (alloc.100 (* '3 '8))])
                                  (begin
                                    (mset!.300 meths.4 '0 stack-push.25)
                                    (mset!.300 meths.4 '8 stack-pop.35)
                                    (mset!.300 meths.4 '16 stack-top.45)
                                    (mset!.300 stack.2 '0 meths.4)
                                    (mset!.300 stack.2 '8 '0)
                                    (mset!.300 stack.2 '16 store.3)
                                    stack.2)))]
                 [invoke.15 (lambda (obj.5 meth-idx.6)
                               (mref.200 (mref.200 obj.5 '0) (* meth-idx.6 '8)))]
                 [stack-push.25 (lambda (self.7 val.8)
                                  (begin
                                    (mset!.300 (mref.200 self.7 '16) 
                                               (* (mref.200 self.7 '8) '8)
                                               val.8)
                                    (mset!.300 self.7 '8 (+ (mref.200 self.7 '8) '1))
                                    self.7))]
                 [stack-pop.35 (lambda (self.9)
                                 (begin
                                   (mset!.300 self.9 '8 (- (mref.200 '8 self.9) '1))
                                   (mref.200 (mref.200 self.9 '16) 
                                             (* (mref.200 self.9 '8) '8))))]
                 [stack-top.45 (lambda (self.209)
                                 (mref.200 (mref.200 self.209 '16) 
                                           (* (- (mref.200 '8 self.209) '1) '8)))])
          (let ([s1.10 (stack-new.0 '10)])
            (begin
              ((invoke.15 s1.10 '0) s1.10 '10) ;; push '10
              ((invoke.15 s1.10 '0) s1.10 '20) ;; push '20
              ((invoke.15 s1.10 '0) s1.10 '30) ;; push ... well you get the idea
              ((invoke.15 s1.10 '0) s1.10 '40)
              ((invoke.15 s1.10 '0) s1.10 '50)
              ((invoke.15 s1.10 '0) s1.10 '60)
              ((invoke.15 s1.10 '0) s1.10 '70)
              ((invoke.15 s1.10 '0) s1.10 '80)
              ((invoke.15 s1.10 '0) s1.10 '90)
              ((invoke.15 s1.10 '0) s1.10 '100)
              (let ([s2.11 (stack-new.0 '6)])
                (begin
                  ((invoke.15 s2.11 '0) s2.11 ((invoke.15 s1.10 '1) s1.10)) ;; push pop
                  ((invoke.15 s1.10 '1) s1.10) ;; pop
                  ((invoke.15 s2.11 '0) s2.11 ((invoke.15 s1.10 '1) s1.10))
                  ((invoke.15 s1.10 '1) s1.10) ;; pop
                  ((invoke.15 s2.11 '0) s2.11 ((invoke.15 s1.10 '1) s1.10))
                  ((invoke.15 s1.10 '1) s1.10) ;; pop
                  ((invoke.15 s2.11 '0) s2.11 ((invoke.15 s1.10 '1) s1.10))
                  ((invoke.15 s1.10 '1) s1.10) ;; pop
                  ((invoke.15 s2.11 '0) s2.11 ((invoke.15 s1.10 '1) s1.10))
                  ((invoke.15 s2.11 '0) s2.11 ((invoke.15 s1.10 '1) s1.10))
                  (let ([x.1000 (+ ((invoke.15 s2.11 '1) s2.11) ((invoke.15 s2.11 '1) s2.11))])
                    (* (+ (let ([x.1001 (+ ((invoke.15 s2.11 '2) s2.11) ((invoke.15 s2.11 '2) s2.11))])
                            (- x.1001 (+ ((invoke.15 s2.11 '1) s2.11) ((invoke.15 s2.11 '1) s2.11))))
                          (let ([x.1002 (+ ((invoke.15 s2.11 '2) s2.11) ((invoke.15 s2.11 '2) s2.11))])
                            (- (+ ((invoke.15 s2.11 '1) s2.11) ((invoke.15 s2.11 '1) s2.11)) x.1002)))
                       x.1000)))))))))
    (letrec ([a.0 (lambda (u.1 v.2 w.3 x.4) 
                    (if (= u.1 '0) 
                        (b.20 v.2 w.3 x.4)
                        (a.0 (- u.1 '1) v.2 w.3 x.4)))]
             [b.20 (lambda (q.5 r.6 x.7)
                    (let ([p.8 (* q.5 r.6)])
                      (e.30 (* q.5 r.6) p.8 x.7)))]
             [c.25 (lambda (x.9) (* '5 x.9))]
             [e.30 (lambda (n.10 p.11 x.12)
                    (if (= n.10 '0) 
                        (c.25 p.11)
                        (o.40 (- n.10 '1) p.11 x.12)))]
             [o.40 (lambda (n.13 p.14 x.15) 
                    (if (= '0 n.13)
                        (c.25 x.15)
                        (e.30 (- n.13 '1) p.14 x.15)))])
      (let ([x.16 '5])
        (a.0 '3 '2 '1 x.16)))
    (letrec ([f.0 (lambda () '80)])
      (let ([a.1 (f.0)] [b.2 (f.0)])
        (* a.1 b.2)))
    (let ([a.1 (letrec ([f.0 (lambda () '80)]) (f.0))]
          [b.2 (letrec ([g.3 (lambda () '50)]) (g.3))])
      (* a.1 b.2))
    (letrec ([f.0 (lambda () '80)]
             [g.3 (lambda () '50)])
      (let ([a.1 (f.0)] [b.2 (g.3)])
        (* a.1 b.2)))
    (letrec ([f.0 (lambda (x.1) (+ x.1 '1))]
             [g.3 (lambda (y.2) (f.0 (f.0 y.2)))])
      (+ (f.0 '1) (g.3 '1)))
    (letrec ([fact.0 (lambda (n.1) 
                       (if (= n.1 '0) '1 (* n.1 (fact.0 (- n.1 '1)))))])
      (fact.0 '10))
    (let ([a.1 '5] [b.2 '1])
      (let ([b.3 (* b.2 a.1)] [a.4 (- a.1 '1)])
        (let ([b.5 (* b.3 a.4)] [a.6 (- a.4 '1)])
          (let ([b.7 (* b.5 a.6)] [a.8 (- a.6 '1)])
            (let ([b.9 (* b.7 a.8)] [a.10 (- a.8 '1)])
              (let ([b.11 (* b.9 a.10)])
                b.11))))))
    (let ([n.1 '5])
      (let ([a.2 '1])
        (let ([a.3 (* a.2 n.1)])
          (let ([n.4 (- n.1 '1)])
            (let ([a.5 (* a.3 n.4)])
              (let ([n.6 (- n.4 '1)])
                (let ([a.7 (* a.5 n.6)])
                  (let ([n.8 (- n.6 '1)])
                    (let ([a.9 (* a.7 n.8)])
                      a.9)))))))))
    (letrec ([double.0 (lambda (a.1) (+ a.1 a.1))])
      (double.0 '10))
    (letrec ([double.0 (lambda (x.1) (* x.1 '2))])
      (begin (double.0 '5)))
    (let ([x.5 (let ([y.10 '10]) (let ([x.15 '15]) (* y.10 x.15)))]) x.5)
    (letrec ([f.0 (lambda (x.1) (+ '1 x.1))]
             [g.15 (lambda (x.2) (- x.2 '1))]
             [t.20 (lambda (x.3) (- x.3 '1))]
             [j.30 (lambda (x.4) (- x.4 '1))]
             [i.40 (lambda (x.5) (- x.5 '1))]
             [h.50 (lambda (x.6) (- x.6 '1))])
      (let ([x.7 '80])
        (let ([a.8 (f.0 x.7)]
              [b.9 (g.15 x.7)]
              [c.10 (h.50 (i.40 (j.30 (t.20 x.7))))])
          (* a.8 (* b.9 (+ c.10 '0))))))
    (letrec ([f.0 (lambda (x.1) (+ '1 x.1))]
             [g.30 (lambda (x.2) (- x.2 '1))])
      (let ([x.7 '80])
        (let ([a.8 (f.0 x.7)]
              [b.9 (g.30 x.7)]
              [c.10 (letrec ([h.50 (lambda (x.6) (- x.6 '1))])
                      (h.50 (letrec ([i.40 (lambda (x.5) (- x.5 '1))])
                             (i.40
                               (letrec ([t.20 (lambda (x.3) (- x.3 '1))]
                                        [j.35 (lambda (x.4) (- x.4 '1))])
                                 (j.35 (t.20 x.7)))))))])
          (* a.8 (* b.9 (+ c.10 '0))))))
    (letrec ([fact.0 (lambda (n.1)
                       (if (= n.1 '0)
                           '1
                           (let ([t.2 (- n.1 '1)])
                             (let ([t.3 (fact.0 t.2)])
                               (* n.1 t.3)))))])
      (fact.0 '10))
    (letrec ([fib.0 (lambda (n.1)
                      (if (if (= '0 n.1) '#t (= '1 n.1))
                          '1
                          (+ (fib.0 (- n.1 '1)) (fib.0 (- n.1 '2)))))])
      (fib.0 '10))
    (letrec ([even.0 (lambda (n.1)
                       (if (= n.1 '0)
                           '1
                           (odd.3 (- n.1 '1))))]
             [odd.3 (lambda (n.2)
                      (if (= n.2 '0)
                          '0
                          (even.0 (- n.2 '1))))])
      (even.0 '17))
    (letrec ()
      (let ([result.3
             (let ([y.2 '10])
               (+ (let ([x.1 '5]) (if (< '11 x.1) (+ x.1 y.2) (+ y.2 '100)))
                  (let ([x.5 '10] [y.4 '20]) (* x.5 y.4))))])
        result.3))
    (letrec () (let ([x.5 '5]) x.5))
    (letrec () (let ([x.5 '5] [y.6 '6]) (+ x.5 y.6)))
    (letrec () (let ([x.5 '5]) (let ([y.6 '6]) (+ x.5 y.6))))
    (letrec ([sqr-double.0 (lambda (z.5)
                             (let ([z.6 (* z.5 z.5)])
                               (double.1 z.6)))]
             [double.1 (lambda (w.4)
                         (let ([w.7 (+ w.4 w.4)])
                           (return.3 w.7)))]
             [return.3 (lambda (result.8) result.8)])
      (begin (sqr-double.0 '3) (sqr-double.0 '5)))
    (letrec ([sum.100 (lambda (x.1 y.2 z.3 w.4)
                        (+ x.1 (+ y.2 (+ z.3 w.4))))])
      (let ([a.6 (make-vector '1)])
        (sum.100 (begin (vector-set! a.6 '0 '1) (vector-ref a.6 '0))
                 (begin (vector-set! a.6 '0 '2) (vector-ref a.6 '0))
                 (begin (vector-set! a.6 '0 '3) (vector-ref a.6 '0))
                 (begin (vector-set! a.6 '0 '4) (vector-ref a.6 '0)))))
    (letrec ([sum.100 (lambda (x.1 y.2 z.3 w.4)
                      (+ x.1 (+ y.2 (+ z.3 w.4))))])
      (let ([a.6 (make-vector '1)])
        (let ([b.7 (begin (vector-set! a.6 '0 '1) (vector-ref a.6 '0))]
              [c.8 (begin (vector-set! a.6 '0 '2) (vector-ref a.6 '0))]
              [d.9 (begin (vector-set! a.6 '0 '3) (vector-ref a.6 '0))]
              [e.10 (begin (vector-set! a.6 '0 '4) (vector-ref a.6 '0))])
          (sum.100 b.7 c.8 d.9 e.10))))
    (letrec ([fact.0 (lambda (n.2) (fact.1 n.2 '1))]
             [fact.1 (lambda (n.3 a.4)
                       (if (= n.3 '0)
                           a.4
                           (fact.1 (- n.3 '1) (* n.3 a.4))))])
      (fact.0 '10))
    (letrec ([make-param.1 (lambda (val.6)
                             (let ([x.2 (cons val.6 (void))])
                               (letrec ([param.3 (lambda (set.4 val.5)
                                                   (if set.4
                                                       (set-car! x.2 val.5)
                                                       (car x.2)))])
                                 param.3)))])
      (let ([p.7 (make-param.1 '10)])
        (begin
          (p.7 '#t '15)
          (p.7 '#f '#f))))
    (let ([x.1 (cons '0 '())])
      (letrec ([inc.2 (lambda () (set-car! x.1 (+ (car x.1) '1)))]
               [dec.3 (lambda () (set-car! x.1 (- (car x.1) '1)))])
        (begin
          (inc.2)
          (dec.3)
          (dec.3)
          (inc.2)
          (inc.2)
          (inc.2)
          (dec.3)
          (inc.2)
          x.1)))
    (letrec ([gcd.0 (lambda (x.1 y.2)
                      (if (= y.2 '0) 
                          x.1 
                          (gcd.0 (if (> x.1 y.2) (- x.1 y.2) x.1)
                                 (if (> x.1 y.2) y.2 (- y.2 x.1)))))])
      (gcd.0 '1071 '1029))
    (letrec ([sub1.1 (lambda (n.2) (- n.2 '1))]
             [fib.0 (lambda (n.3)
                      (if (= '0 n.3)
                          '0
                          (if (= '1 n.3)
                              '1
                              (+ (fib.0 (sub1.1 n.3))
                                 (fib.0 (sub1.1 (sub1.1 n.3)))))))])
      (fib.0 '10))
    (letrec ([ack.0 (lambda (m.1 n.2)
                      (if (= m.1 '0)
                          (+ n.2 '1)
                          (if (if (> m.1 '0) (= n.2 '0) '#f)
                              (ack.0 (- m.1 '1) '1)
                              (let ([tmp.3 (ack.0 m.1 (- n.2 '1))])
                                (ack.0 (- m.1 '1) tmp.3)))))])
      (ack.0 '2 '4))
    (letrec ([ack.0 (lambda (m.1 n.2)
                      (if (= m.1 '0)
                          (+ n.2 '1)
                          (if (if (> m.1 '0) (= n.2 '0) '#f)
                              (ack.0 (- m.1 '1) '1)
                              (ack.0 (- m.1 '1) (ack.0 m.1 (- n.2 '1))))))])
      (ack.0 '2 '4))
    (letrec ([fib.0 (lambda (n.2) (fib.1 n.2 '0 '1))]
             [fib.1 (lambda (n.3 a.4 b.5)
                      (if (= n.3 '0)
                          a.4
                          (fib.1 (- n.3 '1) b.5 (+ b.5 a.4))))])
      (fib.0 '5))
    (letrec ([if-test.1 (lambda ()
                          (let ([x.5 '5])
                            (* (if (= x.5 '5)
                                   (+ x.5 '10)
                                   (- x.5 '10)) '10)))])
       (if-test.1))
    (letrec ([if-test.1 (lambda ()
                          (let ([x.5 (make-vector '2)])
                            (* (if (begin (vector-set! x.5 '1 '5) (= (vector-ref x.5 '1) '5))
                                   (+ (vector-ref x.5 '1) '10)
                                   (- (vector-ref x.5 '1) '10)) '10)))])
       (if-test.1))
    (letrec ([if-test.2 (lambda ()
                          (let ([x.5 (make-vector '1)])
                            (begin
                              (vector-set! x.5 '0
                                (if (begin
                                      (vector-set! x.5 '0 '7)
                                      (if (< (vector-ref x.5 '0) '1)
                                          '#f
                                          (< (vector-ref x.5 '0) '10)))
                                    (* (vector-ref x.5 '0) '2)
                                    (+ (vector-ref x.5 '0) '5)))
                              (vector-ref x.5 '0))))])
      (if-test.2))
    (letrec ([if-test.3 (lambda (n.1)
                          (begin
                            (if (if (= n.1 '0)
                                    '#t
                                    (if (= n.1 '1) '#t (= n.1 '2)))
                                (* n.1 '5)
                                (- n.1 '5))))])
       (if-test.3 '2))
    (letrec ([if-test.4 (lambda (x.5)
                          (begin
                            (* (if (if (= x.5 '10) '#f '#t)
                                   (+ x.5 '10)
                                   (- x.5 '2))
                               '10)))])
      (if-test.4 '2))
    (letrec ([if-test.5 (lambda (n.1 x.2 y.3)
                          (begin
                            (if (= n.1 '0)
                                (vector-set! x.2 '0 (+ (vector-ref x.2 '0) (vector-ref y.3 '0)))
                                (vector-set! y.3 '0 (+ (vector-ref y.3 '0) (vector-ref x.2 '0))))
                            (vector-set! x.2 '0 (+ (vector-ref x.2 '0) n.1))
                            (if (if (= n.1 (vector-ref y.3 '0)) '#f '#t)
                                (+ n.1 (vector-ref x.2 '0))
                                (+ n.1 (vector-ref y.3 '0)))))])
       (let ([q.6 (make-vector '1)] [p.7 (make-vector '1)])
         (begin
           (vector-set! q.6 '0 '1)
           (vector-set! p.7 '0 '2)
           (if-test.5 '3 q.6 p.7))))
    (letrec ([if-test.6 (lambda (n.0)
                           (let ([n.1 (make-vector '1)]
                                 [x.2 (make-vector '1)]
                                 [y.3 (make-vector '1)])
                             (begin
                               (vector-set! n.1 '0 n.0)
                               (vector-set! x.2 '0 '1)
                               (begin
                                 (vector-set! y.3 '0 '1)
                                 (if (= (vector-ref n.1 '0) '0)
                                     (vector-set! (vector-ref x.2 '0) '0 (+ (vector-ref x.2 '0) (vector-ref y.3 '0)))
                                     (vector-set! y.3 '0 (+ (vector-ref y.3 '0) (vector-ref x.2 '0))))
                                 (vector-set! x.2 '0 (+ (vector-ref x.2 '0) (vector-ref n.1 '0))))
                               (if (if (= (vector-ref n.1 '0) (vector-ref y.3 '0)) '#f '#t)
                                   (vector-set! n.1 '0 (+ (vector-ref n.1 '0) (vector-ref x.2 '0)))
                                   (vector-set! n.1 '0 (+ (vector-ref n.1 '0) (vector-ref y.3 '0))))
                               (+ (vector-ref x.2 '0) (vector-ref n.1 '0)))))])
       (if-test.6 '1))
    (letrec ()
       (let ([x.1 '0] [y.2 '1] [z.3 (make-vector '1)])
         (begin
           (if (if (= x.1 '0) (= y.2 '1) '#f)
               (vector-set! z.3 '0 '5)
               (begin (vector-set! z.3 '0 '5) (vector-set! z.3 '0 (+ (vector-ref z.3 '0) (vector-ref z.3 '0)))))
           (vector-ref z.3 '0))))
    (letrec ([main.0 (lambda (x.1 y.2)
                       (let ([z.3 (if (if (= x.1 '1) '#t (= y.2 '1))
                                      '1
                                      '0)])
                         (* z.3 '5)))])
      (main.0 '1 '0))
    (letrec ([main.0 (lambda (a.3 b.4)
                       (let ([a.1 (make-vector '1)] [b.2 (make-vector '1)])
                         (begin
                           (vector-set! a.1 '0 a.3)
                           (vector-set! b.2 '0 b.4)
                           (if (if (= (vector-ref a.1 '0) '1) (= (vector-ref b.2 '0) '1) '#t)
                               (vector-set! a.1 '0 '1)
                               (vector-set! b.2 '0 '0))
                           (vector-set! b.2 '0 (* (vector-ref b.2 '0) '10))
                           (vector-set! a.1 '0 (+ (vector-ref a.1 '0) (vector-ref b.2 '0)))
                           (vector-ref a.1 '0))))])
      (main.0 '0 '1))
    (letrec ([main.0 (lambda (a.1 b.2)
                       (if (if (= a.1 '1) (= b.2 '1) '#t) '1 '0))])
      (main.0 '1 '0))
    (letrec ([main.0 (lambda (a.1 b.2)
                       (if (if (= a.1 '1) (= b.2 '1) '#t) '1 '0))])
      (main.0 '0 '0))
    (letrec ()
       (let ([a.1 '1] [b.2 '1])
         (if (if (= a.1 '1) (= b.2 '1) '#t) '1 '0)))
    (letrec ()
      (let ([n.1 (let ([p.7 (make-vector '1)]) (begin (vector-set! p.7 '0 '1) p.7))])
        (begin
          (let ([a.2 '2])
            (begin
              (let ([b.3 '3])
                (begin
                  (vector-set! n.1 '0 (+ (vector-ref n.1 '0) (if (= (+ (vector-ref n.1 '0) b.3) b.3) '5 '10)))
                  (vector-set! n.1 '0 (+ (vector-ref n.1 '0) b.3))))
              (vector-set! n.1 '0 (+ (vector-ref n.1 '0) a.2))))
          (+ (vector-ref n.1 '0) (vector-ref n.1 '0)))))
    (letrec ()
      (let ([a.1 '1] [b.2 '2] [c.3 '3] [d.4 '4] [e.5 '5])
        (+ (+ (+ (+ e.5 d.4) c.3) b.2) a.1)))
    (letrec ()
      (let ([a.1 '1] [b.2 '2] [c.3 '3] [d.4 '4] [e.5 '5] [f.6 '6])
        (let ([a.7 (if (> (+ a.1 d.4) f.6)
                       (* a.1 (+ c.3 f.6))
                       (* a.1 (+ b.2 e.5)))])
          a.7)))
    (letrec ([dot.0 (lambda (a.1 a.2 a.3 a.4 b.5 b.6 b.7 b.8)
                      (+ (* a.1 b.5) 
                         (+ (* a.2 b.6) 
                            (+ (* a.3 b.7) (* a.4 b.8)))))])
      (dot.0 '2 '4 '6 '8 '1 '3 '5 '7))
    (letrec ([dot-double-first.51 (lambda (a.1 a.2 a.3 a.4 b.5 b.6 b.7 b.8)
                                    (dot.50 (+ a.1 a.1) (+ a.2 a.2)
                                            (+ a.3 a.3) (+ a.4 a.4)
                                            b.5 b.6 b.7 b.8))]
             [dot.50 (lambda (a.11 a.12 a.13 a.14 b.15 b.16 b.17 b.18)
                       (+ (* a.11 b.15) 
                          (+ (* a.12 b.16) 
                             (+ (* a.13 b.17) (* a.14 b.18)))))])
      (dot-double-first.51 '2 '4 '6 '8 '1 '3 '5 '7))
    (letrec ([dot-double-first.51 (lambda (a.1 a.2 a.3 a.4 b.5 b.6 b.7 b.8)
                                    (let ([a.21 (+ a.1 a.1)]
                                          [a.22 (+ a.2 a.2)]
                                          [a.23 (+ a.3 a.3)]
                                          [a.24 (+ a.4 a.4)])
                                      (dot.50 a.21 a.22 a.23 a.24
                                             b.5 b.6 b.7 b.8)))]
             [dot.50 (lambda (a.11 a.12 a.13 a.14 b.15 b.16 b.17 b.18)
                       (+ (* a.11 b.15) 
                          (+ (* a.12 b.16) 
                             (+ (* a.13 b.17) (* a.14 b.18)))))])
      (dot-double-first.51 '2 '4 '6 '8 '1 '3 '5 '7))
    (letrec ((f.1 (lambda (x.2) x.2)))
      (let ((x.3 '1) (y.4 '2))
        (let ((z.5 (f.1 x.3)))
          (let ((w.6 (+ x.3 y.4)))
            (let ((q.7 (f.1 w.6)))
              (+ z.5 q.7))))))
    (letrec ()
      (let ([a.1 '1]
            [b.2 '2]
            [c.3 '3]
            [d.4 '4]
            [e.5 '5]
            [f.6 '6]
            [g.7 '7]
            [h.8 '8]
            [i.9 '9]
            [j.10 '10]
            [k.11 '11]
            [l.12 '12]
            [m.13 '13])
        (let ([a.51 (+ (- (+ a.1 b.2) (+ (- c.3 d.4) e.5)) f.6)])
          (let ([a.52 (+ (- a.51 g.7) (+ h.8 (- i.9 (+ j.10 k.11))))])
            (let ([a.53 (+ a.52 (+ l.12 m.13))])
              (let ([n.14 '14]
                    [o.15 '15]
                    [p.16 '16]
                    [q.17 '17]
                    [r.18 '18]
                    [s.19 '19]
                    [t.20 '20]
                    [u.21 '21]
                    [v.22 '22]
                    [w.23 '23]
                    [x.24 '24]
                    [y.25 '25])
                (let ([a.54 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ a.53
                                                                n.14)
                                                             o.15)
                                                          p.16)
                                                       q.17)
                                                    r.18)
                                                 s.19)
                                              t.20)
                                           u.21)
                                        v.22)
                                     w.23)
                                  x.24)
                               y.25)])
                  (let ([z.26 '26]
                        [b.82 '27]
                        [c.83 '28]
                        [d.84 '29]
                        [e.85 '30]
                        [f.86 '31]
                        [g.87 '32]
                        [h.88 '33]
                        [i.89 '34]
                        [j.810 '35]
                        [k.811 '36]
                        [l.812 '37])
                    (+ a.54
                       (+ z.26
                          (+ b.82
                             (+ c.83
                                (+ d.84
                                   (+ e.85
                                      (+ f.86
                                         (+ g.87
                                            (+ h.88
                                               (+ i.89
                                                  (+ j.810
                                                     (+ k.811
                                                        l.812))))))))))))))))))))
    (letrec ()
      (let ([a.1 '1] [b.2 '2])
        (let ([c.3 a.1] [d.4 '4] [e.5 '5] [f.6 b.2])
          (let ([f.16 (+ f.6 c.3)])
            (let ([f.26 (+ f.16 d.4)])
              (let ([f.36 (+ f.26 e.5)] [g.7 '7])
                (+ f.36 g.7)))))))
    (letrec ()
      (let ([h.8 '77] [i.9 '88] [j.10 '99] [k.11 '111] [a.1 '1] [b.2 '2])
        (let ([c.3 a.1] [d.4 '4] [e.5 '5] [f.6 b.2])
          (let ([f.16 (+ f.6 c.3)])
            (let ([f.26 (+ f.16 d.4)])
              (let ([f.36 (+ f.26 e.5)] [g.7 '7])
                (let ([f.46 (+ f.36 g.7)])
                  (let ([f.56 (+ f.46 i.9)])
                    (let ([f.66 (+ f.56 j.10)])
                      (let ([f.76 (+ f.66 k.11)])
                        (+ f.76 h.8)))))))))))
    (letrec ()
      (let ([a.1 '1]
            [b.2 '2]
            [c.3 '3]
            [d.4 '4]
            [e.5 '5]
            [f.6 '6]
            [g.7 '7]
            [h.8 '8]
            [i.9 '9]
            [j.10 '10]
            [k.11 '11]
            [l.12 '12]
            [m.13 '13]
            [n.14 '14]
            [o.15 '15]
            [p.16 '16]
            [q.17 '17]
            [r.18 '18]
            [s.19 '19]
            [t.20 '20]
            [u.21 '21]
            [v.22 '22]
            [w.23 '23]
            [x.24 '24]
            [y.25 '25]
            [z.26 '26])
        (let ([a.101 (+ a.1 (+ b.2 (+ c.3 (+ d.4 (+ e.5 (+ f.6 (+ g.7 (+ h.8
                     (+ i.9 (+ j.10 (+ k.11 (+ l.12 (+ m.13 (+ n.14 (+ o.15 
                     (+ p.16 (+ q.17 (+ r.18 (+ s.19 (+ t.20 (+ u.21 (+ v.22 
                     (+ w.23 (+ x.24 (+ y.25 z.26)))))))))))))))))))))))))]
              [b.202 '27]
              [c.203 '28]
              [d.204 '29]
              [e.205 '30]
              [f.206 '31]
              [g.207 '32]
              [h.208 '33]
              [i.209 '34]
              [j.2010 '35]
              [k.2011 '36]
              [l.2012 '37]
              [m.2013 '38]
              [n.2014 '39]
              [o.2015 '40])
          (let ([a.102 (+ a.101 (+ b.202 (+ c.203 (+ d.204 (+ e.205 (+ f.206 (+ g.207 (+ h.208
                       (+ i.209 (+ j.2010 (+ k.2011 (+ l.2012 (+ m.2013 
                       (+ n.2014 o.2015))))))))))))))])
            (+ a.102 a.1)))))
   ;; test the basic jump cases -- in value/tail
    (letrec () (if '#t '#t '#f)) ; nb: autograder assumes this is first optimize-jumps test
    (letrec () (if '#f '#t '#f))
    (letrec ()
      (let ([x.1 '3])
        (if (if (= x.1 '3) '#f '#t) '#t '#f)))
    (letrec ()
      (let ([x.1 '3])
        (if (if (= x.1 '3) '#t '#f) '#t '#f)))
    (letrec ()
      (let ([x.1 '3])
        (if (if (= x.1 '4) '#t '#f) '#t '#f)))
    (letrec ()
      (let ([x.1 '3])
        (if (if (= x.1 '4) '#f '#t) '#t '#f)))
    (letrec ()
      (let ([x.1 '3] [y.2 '2])
        (if (if (= x.1 '3) (= y.2 '2) '#f) '#t '#f)))
    (letrec ()
      (let ([x.1 '3] [y.2 '2])
        (if (if (= x.1 '3) '#t (= y.2 '2)) '#t '#f)))
    (letrec ()
      (let ([x.1 '3] [y.2 '2])
        (if (if (= x.1 '3) '#f (= y.2 '2)) '#t '#f)))
    (letrec ()
      (let ([x.1 '3] [y.2 '2])
        (if (if (= x.1 '3) (= y.2 '2) '#t) '#t '#f)))
    ;; testing the basic jump cases -- in effect
    (letrec ()
      (let ([ls.1 (cons '1 '2)])
        (begin
          (if (pair? ls.1) (set-cdr! ls.1 (+ (cdr ls.1) '1)) (void))
          ls.1)))
    (letrec ()
      (let ([ls.1 (cons '1 '2)] [x.2 '10])
        (begin
          (if (pair? ls.1) (void) (set-cdr! ls.1 x.2))
          ls.1)))
    ;; more complicated tests 
    (letrec ()
      (let ([x.1 '7] [y.2 '4])
        ;; (or (and (fixnum? x.1) (= x.1 4) (fixnum? y.2) (= y.2 7))
        ;;     (and (fixnum? x.1) (= x.1 7) (fixnum? y.2) (= y.2 4)))
        (if (if (if (fixnum? x.1) 
                  (if (= x.1 '4) 
                    (if (fixnum? y.2)
                      (= y.2 '7)
                      '#f)
                    '#f)
                  '#f)
              '#t
              (if (fixnum? x.1)
                (if (= x.1 '7)
                  (if (fixnum? y.2)
                    (= y.2 '4)
                    '#f)
                  '#f)
                '#f))
          '#t
          '#f)))
    (letrec ([num-list?.0 (lambda (ls.1)
                            (if (null? ls.1)
                                '#t
                                (if (fixnum? (car ls.1))
                                    (num-list?.0 (cdr ls.1))
                                    '#f)))]
             [length.100 (lambda (ls.4)
                           (if (null? ls.4)
                               '0
                               (+ (length.100 (cdr ls.4)) '1)))]
             [dot-prod.200 (lambda (ls1.5 ls2.6)
                             (if (if (null? ls1.5) (null? ls2.6) '#f)
                                 '0
                                 (+ (* (car ls1.5) (car ls2.6))
                                    (dot-prod.200 (cdr ls1.5) (cdr ls2.6)))))])
      (let ([ls1.2 (cons '1 (cons '2 (cons '3 (cons '4 (cons '5 '())))))]
            [ls2.3 (cons '5 (cons '4 (cons '3 (cons '2 (cons '1 '())))))])
        (if (if (if (eq? (num-list?.0 ls1.2) '#f) '#f '#t)
                (if (if (eq? (num-list?.0 ls2.3) '#f) '#f '#t)
                    (= (length.100 ls1.2) (length.100 ls2.3))
                    '#f)
                '#f)
            (dot-prod.200 ls1.2 ls2.3)
            '#f)))
    (letrec ([num-list?.0 (lambda (ls.1)
                            (if (null? ls.1)
                                '#t
                                (if (fixnum? (car ls.1))
                                    (num-list?.0 (cdr ls.1))
                                    '#f)))]
             [map.10 (lambda (lab.3 ls.4)
                      (if (null? ls.4) 
                          '()
                          (cons (lab.3 (car ls.4)) (cdr ls.4))))]
             [square.20 (lambda (n.5) (* n.5 n.5))])
      (let ([ls.2 (cons '1 (cons '2 (cons '3 (cons '4 (cons '5 '())))))])
        (begin
          (if (if (eq? (num-list?.0 ls.2) '#f) '#f '#t)
              (set-car! ls.2 (map.10 square.20 ls.2))
              (void))
          ls.2)))
    (letrec ([num-list?.0 (lambda (ls.1)
                            (if (null? ls.1)
                                '#t
                                (if (fixnum? (car ls.1))
                                    (num-list?.0 (cdr ls.1))
                                    '#f)))]
             [list-product.3 (lambda (ls.4)
                               (if (null? ls.4)
                                   '1
                                   (* (car ls.4) 
                                      (list-product.3 (cdr ls.4)))))])
      (let ([ls.2 (cons '1 (cons '2 (cons '3 (cons '4 (cons '5 '())))))])
        (if (num-list?.0 ls.2)
            (list-product.3 ls.2)
            '#f)))

    (let ([pair.5 (cons '1 '2)])
      (begin
        (set-car! pair.5 (set-cdr! pair.5 '10))
        pair.5))

    (letrec ([list4.0 (lambda (a.1 b.2 c.3 d.4)
                        (cons a.1 (cons b.2 (cons c.3 (cons d.4 '())))))])
      (let ([pair.5 (cons '1 '2)] [vect.6 (make-vector '3)])
        (list4.0 (set-car! pair.5 '7) (set-cdr! pair.5 '10)
                 (vector-set! vect.6 '0 '16) '()))) 

    (letrec ([f.3 (lambda (x.15 y.14)
                    (if x.15
                        (h.1 (+ x.15 y.14))
                        (g.2 (+ x.15 '1) (+ y.14 '1))))]
             [g.2 (lambda (u.6 v.5)
                    (let ([a.8 (+ u.6 v.5)] [b.7 (* u.6 v.5)])
                      (letrec ([e.9 (lambda (d.10)
                                      (let ([p.12 (cons a.8 b.7)])
                                        (letrec ([q.11 (lambda (m.13)
                                                         (if (< m.13 u.6)
                                                             (f.3 m.13 d.10)
                                                             (h.1 (car p.12))))])
                                          (q.11 (f.3 a.8 b.7)))))])
                        (e.9 u.6))))]
             [h.1 (lambda (w.4) w.4)])
      (f.3 '4 '5))

    (let ([y.17 '()] [z.1 '10])
      (let ([y.2 (cons y.17 (void))])
        (let ([test-ls.16 (cons '5 (car y.2))])
          (let ([test-ls.3 (cons test-ls.16 (void))])
            (begin
              (set-car!
                y.2
                (letrec ([anon.24 
                           (lambda (f.4)
                             ((letrec ([anon.23 
                                         (lambda (g.7)
                                           (f.4 (letrec ([anon.22 (lambda (x.8)
                                                                    ((g.7 g.7)
                                                                     x.8))])
                                                  anon.22)))])
                                anon.23)
                              (letrec ([anon.21 
                                         (lambda (g.5)
                                           (f.4 (letrec ([anon.20 (lambda (x.6)
                                                                    ((g.5 g.5)
                                                                     x.6))])
                                                  anon.20)))])
                                anon.21)))])
                  anon.24))
              (set-car! test-ls.3 (cons z.1 (car test-ls.3)))
              (let ([length.15 (void)])
                (let ([length.9 (cons length.15 (void))])
                  (begin
                    (letrec ([length.14 (lambda (ls.10)
                                          (if (null? ls.10)
                                              '0
                                              (+ '1
                                                 ((car length.9)
                                                  (cdr ls.10)))))])
                      (set-car! length.9 length.14))
                    (let ([len.11 ((car length.9) (car test-ls.3))])
                      (eq? (begin
                             (set-car!
                               length.9
                               ((car y.2)
                                (letrec ([anon.19
                                           (lambda (len.12)
                                             (letrec ([anon.18 
                                                        (lambda (ls.13)
                                                          (if (null? ls.13)
                                                              '0
                                                              (+ '1
                                                                 (len.12
                                                                   (cdr
                                                                     ls.13)))
                                                              ))])
                                               anon.18))])
                                  anon.19)))
                             ((car length.9) (car test-ls.3)))
                           len.11))))))))))

    (letrec ([curry-list.100
               (lambda (x.1)
                 (letrec ([c-list.110
                            (lambda (y.2)
                              (letrec ([c-list.120
                                         (lambda (z.3)
                                           (letrec ([c-list.130
                                                      (lambda (w.4)
                                                        (cons x.1 
                                                          (cons y.2 
                                                            (cons z.3
                                                              (cons w.4 '())))))])
                                             c-list.130))])
                                c-list.120))])
                   c-list.110))]
             [append.200 (lambda (ls1.5 ls2.6)
                           (if (null? ls1.5)
                               ls2.6
                               (cons (car ls1.5)
                                     (append.200 (cdr ls1.5) ls2.6))))])
      (append.200
        ((((curry-list.100 '1) '2) '3) '4)
        ((((curry-list.100 '5) '6) '7) '8)))

    (let ([g.1 (+ '5
                  ((letrec ([anon.10 (lambda (w.4 u.3) (+ w.4 u.3))])
                     anon.10)
                   '8
                   '9))])
      (letrec ([f.2 (lambda (x.5)
                      (+ x.5
                         (((letrec ([anon.9 (lambda (y.6)
                                              (letrec ([anon.8 
                                                         (lambda (z.7)
                                                           (+ y.6 z.7))])
                                                anon.8))])
                             anon.9)
                           '6)
                          '7)))])
        g.1))

    (let ([test.1 (if (if '10 '#f '#t) '5 '#f)])
      (let ([num.8 (void)])
        (let ([num.3 (cons num.8 (void))])
          (letrec ([length.2 (lambda (ls.4)
                               (let ([len.6 
                                       (if ((letrec ([anon.9 
                                                       (lambda (ck.5)
                                                         (begin
                                                           ck.5
                                                           (set-car!
                                                             num.3 test.1)
                                                           ck.5))])
                                              anon.9)
                                            (null? ls.4))
                                         (begin
                                           (car num.3)
                                           (set-car! num.3 '0)
                                           (car num.3))
                                         (begin
                                                (length.2 '())
                                                (set-car! num.3 '5)
                                                (+ '1
                                                   (length.2
                                                     (cdr ls.4)))))])
                               (if len.6 len.6 (void))))])
          (begin
            (let ([num.7 '5]) (set-car! num.3 num.7))
            (length.2
              (cons
                '5
                (cons
                  (if (set-car! num.3 '50) (length.2 (cons test.1 '())) '1)
                  '()))))))))

(letrec ([quotient.1 (lambda (x.3 y.2)
                         (if (< x.3 '0)
                             (- '0 (quotient.1 (- '0 x.3) y.2))
                             (if (< y.2 '0)
                                 (- '0 (quotient.1 x.3 (- '0 y.2)))
                                 (letrec ([f.4 (lambda (x.6 a.5)
                                                 (if (< x.6 y.2)
                                                     a.5
                                                     (f.4 (- x.6 y.2)
                                                          (+ a.5 '1))))])
                                   (f.4 x.3 '0)))))])
    (let ([sub-interval.9 '1])
      (letrec ([sub-and-continue.8 (lambda (n.15 acc.14 k.13)
                                     (k.13
                                       (- n.15 sub-interval.9)
                                       (* n.15 acc.14)))]
               [strange-fact.7 (lambda (n.11 acc.10)
                                 (if (= n.11 '0)
                                     (letrec ([anon.26 (lambda (proc.12)
                                                         (proc.12
                                                           acc.10))])
                                       anon.26)
                                     (sub-and-continue.8
                                       n.11
                                       acc.10
                                       strange-fact.7)))])
        (let ([x.24 '20]
              [fact.18 (let ([seed.16 '1])
                         (letrec ([anon.25 (lambda (n.17)
                                             (strange-fact.7
                                               n.17
                                               seed.16))])
                           anon.25))])
          (let ([x.19 (cons x.24 (void))])
            (letrec ([answer-user.21 (lambda (ans.20)
                                       (quotient.1 ans.20 (car x.19)))])
              (let ([give-fact5-answer.23 (fact.18 '5)]
                    [give-fact6-answer.22 (fact.18 '6)])
                (begin
                  (set-car! x.19 (give-fact5-answer.23 answer-user.21))
                  (set-car! x.19 (give-fact6-answer.22 answer-user.21))
                  (car x.19)))))))))


    (letrec ([f.1 (lambda ()
                  (letrec ([loop.2 (lambda (link.3)
                                     (letrec ([anon.5 (lambda ()
                                                        (link.3))])
                                       anon.5))])
                    (loop.2
                      (letrec ([anon.4 (lambda () '668)]) anon.4))))])
      ((f.1)))

    (letrec ([loop.1 (lambda ()
                       (letrec ([anon.2 (lambda () (loop.1))]) anon.2))])
      (begin (loop.1) '0))

    (if (letrec ([anon.6 (lambda () '1)]) anon.6)
      (let ([a.4 '2])
        (let ([a.1 (cons a.4 (void))])
          (if (if ((letrec ([anon.5 (lambda (x.2)
                                      (let ([x.3 (set-car!
                                                   a.1
                                                   (set-car! a.1 '1))])
                                        x.3))])
                     anon.5)
                    '1)
                  (if (eq? (car a.1) (void)) '#t '#f)
                  '#f)
              '778477
              '14629)))
      (void))

    (letrec ([dropsearch.8 
               (lambda (cell.29 tree.28)
                 (letrec ([create-link.31 
                            (lambda (node.35 f.34)
                              (letrec ([anon.45 
                                         (lambda (g.36)
                                           (if (pair? node.35)
                                               (if (eq? node.35 cell.29)
                                                   '#f
                                                   (f.34
                                                     (create-link.31
                                                       (car node.35)
                                                       (create-link.31
                                                         (cdr node.35)
                                                         g.36))))
                                               (f.34 g.36)))])
                                anon.45))]
                          [loop.30 
                            (lambda (link.32)
                              (letrec ([anon.44
                                         (lambda ()
                                           (if link.32
                                               (loop.30
                                                 (link.32
                                                   (letrec ([anon.43
                                                              (lambda (v.33)
                                                                v.33)])
                                                     anon.43)))
                                               '#f))])
                                anon.44))])
                   (loop.30
                     (create-link.31
                       tree.28
                       (letrec ([anon.42 (lambda (x.37) x.37)])
                         anon.42)))))]
             [racethunks.7 (lambda (thunkx.27 thunky.26)
                             (if (if thunkx.27 thunky.26 '#f)
                                 (racethunks.7 (thunkx.27) (thunky.26))
                                 (if thunky.26 '#t (if thunkx.27 '#f '()))))]
             [higher?.6 (lambda (x.25 y.24 tree.23)
                          (racethunks.7
                            (dropsearch.8 x.25 tree.23)
                            (dropsearch.8 y.24 tree.23)))]
             [under?.5 (lambda (x.22 y.21 tree.20)
                         (racethunks.7
                           (dropsearch.8 x.22 y.21)
                           (dropsearch.8 x.22 tree.20)))]
             [explore.4 (lambda (x.18 y.17 tree.16)
                          (if (pair? y.17)
                              (if (eq? x.18 y.17)
                                  '#f
                                  (let ([result.19 (higher?.6
                                                     x.18
                                                     y.17
                                                     tree.16)])
                                    (if (eq? result.19 '#t)
                                        (if (explore.4 y.17 (car y.17) tree.16)
                                            (explore.4 y.17 (cdr y.17) tree.16)
                                            '#f)
                                        (if (eq? result.19 '#f)
                                            (process-vertical-jump.3
                                              x.18 y.17 tree.16)
                                            (if (eq? result.19 '())
                                                (process-horizontal-jump.2
                                                  x.18 y.17 tree.16)
                                                (void))))))
                              '#t))]
             [process-vertical-jump.3 (lambda (jumpedfrom.15 jumpedto.14 tree.13)
                                        (if (under?.5 jumpedfrom.15
                                                      jumpedto.14 tree.13)
                                            '#f
                                            (fullfinite?.1 jumpedto.14)))]
             [process-horizontal-jump.2 (lambda (jumpedfrom.12
                                                  jumpedto.11 tree.10)
                                          (fullfinite?.1 jumpedto.11))]
             [fullfinite?.1 (lambda (pair.9)
                              (if (pair? pair.9)
                                   (if (explore.4 pair.9 (car pair.9) pair.9)
                                       (explore.4 pair.9 (cdr pair.9) pair.9)
                                       '#f)
                                   '#t))])
      (cons
        (fullfinite?.1 (cons '1 '2))
        (cons
          (fullfinite?.1
            (let ([x.41 (cons '1 '2)])
              (begin (set-car! x.41 x.41) x.41)))
          (cons
            (fullfinite?.1
              (let ([a.40 (cons '0 '0)]
                    [b.39 (cons '0 '0)]
                    [c.38 (cons '0 '0)])
                (begin
                  (set-car! a.40 b.39)
                  (set-cdr! a.40 c.38)
                  (set-cdr! b.39 c.38)
                  (set-car! b.39 c.38)
                  (set-car! c.38 b.39)
                  (set-cdr! c.38 b.39)
                  a.40)))
            '()))))

  ;; Thiago Rebello
    (let ([t.7 '1])
      (letrec ([a.1 (lambda (x.2) (if (> x.2 '5) (b.3 x.2) (c.5 x.2)))]
               [b.3 (lambda (y.4) (cons y.4 '()))]
               [c.5 (lambda (z.6) (a.1 (+ z.6 t.7)))])
        (a.1 '0)))
    
    ;; Chabane Maidi
    (letrec ([p.1 (lambda (p.2 p.3) 
                    (if (< '1 '10) 
                        (letrec ([p.4 (lambda (p.5) (+ p.5 '10))]) (p.4 p.3))
                        p.2))]
             [p.6 (lambda (p.7) (+ p.7 '10))])
      (p.1 (+ (p.6 '16) '19) (p.1 '11 '15)))

    ;; Kewal Karavinkoppa
    (letrec ([ack.1 (lambda (n.2 m.3)
                      (if (= '0 n.2)
                          (+ '1 m.3)
                          (if (= '0 m.3)
                              (ack.1 (- n.2 '1) '1)
                              (ack.1 (- n.2 '1) (ack.1 n.2 (- m.3 '1))))))])
      (ack.1 '2 '3))

    ;; Shiv Indap
    (letrec ([fact.0 (lambda (n.3 k.4)
                       (if (eq? n.3 '0)
                           (k.4 '1)
                           (fact.0 (- n.3 '1)
                                   (letrec ([anon.5 (lambda (v.6)
                                                      (k.4 (* n.3 v.6)))])
                                     anon.5))))]
             [anon.1 (lambda (v.2) v.2)])
      (fact.0 '5 anon.1))
    
    ;; Patrick Jensen
    (let ([a.1 '1])
      (letrec ([f.3 (lambda (b.2) (+ b.2 a.1))])
        (if (procedure? a.1)
            (+ (f.3 a.1) (f.3 '2))
            (if (procedure? f.3)
               (let ([c.4 (f.3 '3)])
                 (if (procedure? c.4) (cons c.4 '()) (* c.4 a.1)))
               (cons a.1 '())))))

    ;; Emily Lyons
    (letrec ([insert.0 (lambda (item.1 index.2 ls.3)
                         (if (= '0 index.2)
                             (cons item.1 ls.3)
                             (cons
                               (car ls.3)
                               (insert.0 item.1 (- index.2 '1) (cdr ls.3)))))])
      (insert.0
        '3
        '2
        (cons '1 (cons '2 (cons '4 (cons '5 '()))))))

    ;; Yu-Shan Huang
    (let ([x.1 '6])
      (letrec ([f.2 (lambda () x.1)])
        (letrec ([f.3 (lambda (y.5) (+ (f.2) x.1))])
          (cons (f.3 f.2) (f.2)))))
    
    ;; Melanie Dybvig 
    (let ([e.5 '7])
      (letrec ([a.1 (lambda (x.6) (cons x.6 x.6))]
               [b.2 (lambda (x.7)
                      (cons  x.7 (if (procedure? a.1) (a.1 x.7) '#f)))]
               [c.3 (lambda (x.8) (b.2 (a.1 x.8)))]
               [d.4 (lambda (x.9) (c.3 (b.2 x.9)))])
        (cons e.5 (cons (d.4 e.5) '()))))
    

    ;; Francis Fernandez
    (let ([test.0 (* '0 '5)])
      (let ([true.1 '#t] [false.2 '#f])
        (letrec ([match-test.3 (lambda (test-arg.4)
                                 (if (eq? test-arg.4 test.0) true.1 '-1))])
          (if test.0 (match-test.3 test.0) (match-test.3 false.2)))))

    ;; Greg Smith
    (let ([a.9 '1])
      (letrec ([f.1 (lambda (x.3)
                      (letrec ([f.2 (lambda (y.4) (cons x.3 y.4))]) f.2))])
        (letrec ([f.5 (lambda () (if (f.6) (f.7) (f.8)))]
                 [f.6 (lambda () (if (f.7) (f.8) '#f))]
                 [f.7 (lambda () (if (f.8) '2 '#f))]
                 [f.8 (lambda () (if a.9 '3 '#f))])
          ((f.1 (f.5)) (f.6)))))
    

    ;; Brennon York
    (+ (letrec ([f.1 (lambda () (+ '2 '3))]
                [f.2 (lambda (x.3)
                       (letrec ([f.4 (lambda (y.6) (+ (+ y.6 x.3) (f.1)))])
                         (f.4 '7)))])
         (f.2 '4))
       '5)
    
    ;; Yin Wang
    (let ([a.1 (letrec ([c.4 (lambda ()
                               (letrec ([f.0 (lambda () '80)]) (f.0)))])
                 (c.4))]
          [b.2 (letrec ([d.5 (lambda ()
                               (letrec ([g.3 (lambda () '50)]) (g.3)))])
                 (d.5))])
      (* a.1 b.2))
    
    ;; Leah Brown 
    (let ([v.5 (cons '1000 '1000)])
      (letrec ([f.1 (lambda (v.4) (set-car! v.4 (+ '1 (car v.4))))])
        (letrec ([f.2 (lambda (v.3) (set-cdr! v.3 (- '1 (cdr v.3))))])
          (begin
            (f.1 v.5)
            (f.2 v.5)
            v.5))))

    ;; Nilesh Mahajan
    (letrec ([sum.2 (lambda (x.1)
                      (if (eq? x.1 '0) 
                          '0 
                          (+ x.1 (sum.2 (- x.1 '1)))))])
      (sum.2 '10))

    ;;; P523
    ;;; Zhou Li
    ;;; Test case for Assignment 12
    ;;; Test the letrec clause uder if
    (let ([x.1 '3])
      (letrec ([f.2 (lambda (y.3)
                      (letrec ([g.4 (lambda (z.5)
                                      (if (< z.5 '3)
                                          (letrec ([h.6 (lambda (i.7)
                                                          (+ i.7 i.7))]) h.6)
                                          (+ z.5 z.5)))])
                        g.4))])
        ((f.2 '5) '7)))
    ))
