(load "nanokanren.scm")
(load "ednoc.scm")

(define-syntax test
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (let* ((expected expected-result)
            (produced tested-expression))
       (if (equal? expected produced)
           (printf "~s works!\n" title)
           (error
            'test
            "Failed ~s: ~a\nExpected: ~a\nComputed: ~a"
            title 'tested-expression expected produced))))))

;; ednoc tests

(test 'ednoc-1
  (run 10 (q)
    (ednoc
      [(== q 5) (== q 6)]
      [(== q 6) (== q 5)]))
  '(5 6))

(test 'ednoc-2
  (run 10 (q)
    (ednoc
     [(== q 5)]
     [(== q 6)]))
  '())

(test 'ednoc-3
  (run 5 (q)
    (ednoc
      [(== q 3) (== q 3) (== q 3) (== q 3)]
      [(== q 4)]
      [(== q 5) (== q 5)]
      [(== q 6)]))
  '())

(test 'ednoc-4
  (run 10 (q)
    (ednoc
     [(== q 5) (== q 6) (== q 7)]
     [(== q 5) (== q 6) (== #f #f)]
     [(== q 5) (== q 6) (== #f #f)]))
  '(5 5 5 5 6 6 6 6 7))

(test 'ednoc-5
  (let ([x (var 'x)]
        [y (var 'y)])
    (run 10 (q)
      (ednoc
        [(== x 3) (== y 4)]
        [(== x 5) (== y 6)])
      (== `(,x ,y) q)))
  '((3 6) (5 4)))

(test 'ednoc-6
  (let ([w (var 'w)]
        [x (var 'x)]
        [y (var 'y)])
    (run 10 (q)
      (ednoc
        [(== w 2) (== x 3) (== y 4)]
        [(== w 5) (== x 6) (== y 7)])
      (== `(,w ,x ,y) q)))
  '((2 6 _.0) (2 _.0 7) (5 3 _.0) (_.0 3 7) (5 _.0 4) (_.0 6 4)))

(define foo
  (lambda (x)
    (ednoc
     ((== 1 x) (== 2 x))
     ((== 2 x) (foo 2)))))

(test 'ednoc-7
  (run 2 (q) (foo q))
  '(1 1))

(test 'ednoc-8
  (run 3 (q) (foo q))
  '(1 1 1))

(test 'ednoc-9
  (letrec ([foo (lambda (a d)
                  (ednoc
                   [(== a 'x) (== a 'y)]
                   [(== d '()) (foo a d)]))])
    (let ([a (var 'a)]
          [d (var 'd)])
      (run 10 (q)
        (foo a d)
        (== `(,a . ,d) q))))
  '((x) (x) (x) (x) (x) (x) (x) (x) (x) (x)))

(test 'ednoc-10
  (letrec ([foo (lambda (a d)
                  (ednoc
                    [(== d '()) (foo a d)]
                    [(== a 'x) (== a 'y)]))])
    (let ([a (var 'a)]
          [d (var 'd)])
      (run 10 (q)
        (foo a d)
        (== `(,a . ,d) q))))
  '((x) (y) (x) (y) (x) (y) (x) (y) (x) (y)))

(letrec ([alwayso (lambda (x)
                    (conde
                      [(== #f #f)]
                      [(alwayso x)]))])
  (test 'ednoc-11
    (run 10 (q)
      (ednoc
        [(alwayso q)]
        [(== q 5)]))
    '(5 5 5 5 5 5 5 5 5 5)))

; Vanilla conde tests for completeness--no surprises here.

(test 'conde-1
  (run 3 (q)
    (conde
      [(== q 5) (== q 5)]))
  '(5))

(test 'conde-2
  (run 5 (q)
    (conde
      [(== q 3) (== q 4)]
      [(== q 5)]))
  '(5))

(test 'conde-3
  (run 5 (q)
    (conde
      [(== q 5)]
      [(== q 6)]))
  '(5 6))

(test 'conde-4
  (run 5 (q)
    (conde
      [(== q 5) (== q 5)]
      [(== q 6) (== q 6)]))
  '(5 6))

(test 'conde-5
  (run 5 (q)
    (conde
      [(== q 5) (== q 6)]
      [(== q 6) (== q 6)]))
  '(6))

(test 'conde-6
  (run 5 (q)
    (conde
      [(== q 6) (== q 6)]
      [(== q 5) (== q 6)]))
  '(6))

(test 'conde-7
  (run 10 (q)
    (conde
      [(== q 6)]
      [(== q 5)]
      [(== q 4)]
      [(== q 3)]
      [(== q 2)]))
  '(6 5 4 3 2))

(test 'conde-8
  (run 10 (q)
    (conde
      [(== q 6) (== q 6) (== q 6) (== q 6)]
      [(== q 5) (== q 5) (== q 5) (== q 5)]
      [(== q 4) (== q 4) (== q 4) (== q 4)]
      [(== q 3) (== q 3) (== q 3) (== q 3)]
      [(== q 2) (== q 2) (== q 2) (== q 2)]))
  '(6 5 4 3 2))
