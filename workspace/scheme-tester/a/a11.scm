;;----------------------------------
;; B521 - Assignment 11
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    0002560797
;; Email: sekanaya@indiana.edu
;;----------------------------------


;----------------------------------------------------------------
; Test macro (taken happily from the assignment itself :))
; ---------------------------------------------------------------
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
 
(define-syntax multi-test
  (syntax-rules ()
    ((_ title tested-expression expected-result* ...)
     (let* ((expected* expected-result*)
            ...
            (produced tested-expression))
       (cond
         [(equal? produced expected-result*) (printf "~s works!\n" title)]
         ...
         [else (error
                'test
                "Failed ~s: ~a\nComputed: ~a"
                title 'tested-expression produced)])))))



;=================================================Part II==================================================
;--------------------------------------------------------------------------------------
;Q1)
(run 2 (q)
  (== 5 q)
  (conde
    [(conde
       [(== 5 q) (== 6 q)]) (== 5 q)]
    [(== q 5)]))

; ans: (5)
; reason:
;   1. First unification succeeds and sets fresh variable q to 5.
;   2. The first line of outer conde has the inner conde as the question.
;   3. The question of the only line in the inner conde succeeds as q is 5. However, the answer goal fails
;      and thus the entire conde fails (since it's the only line). This failure leads to the failure of the
;      first conde line in the outer conde.
;   4. The second line of the outer conde is evaluated resulting a success as q is 5.
;   5. There are no goals left to achieve thus the single value associated with q is returned even though two
;      results for q is expected.
;--------------------------------------------------------------------------------------
;Q2)
;;(run* (q)
;;  (exist (x y)
;;    (== `(,x ,y) q) ; <------------------- A
;;    (conde
;;      [fail succeed] ; <------------------ B
;;      [(conde
;;         [(== 5 x) (== y x)] ; <---------- C 
;;         [(== `(,x) y)] ; <--------------- D
;;         [(== x y)])] ; <----------------- E
;;      [succeed]))) ; <-------------------- F

; ans: ((_.0 _.1) (5 5) (_.0 (_.0)) (_.0 _.0))
; reason:
;   1. A succeeds with setting q to (_.0 _.1). The two values indicates the values of the fresh variables
;      x and y.
;   2. B fails and end of story for that line
;   3. C succeeds as x and y are fresh. It sets x to 5 and y to x. Thus q gets another value (5 5)
;   4. D succeeds as x and y are considered as fresh again. The value of x is _.0 and the value of
;      y is the list containing the value of x, i.e. (_.0). Thus, q gets another value as (_.0 (_.)).
;   5. E succeeds as x and y are considered fresh once again and unifies x with y. Since both of them are
;      fresh they unifiy with _.0 which gives q another value of (_.0 _.0).
;   6. F succeeds and ends the outer conde.
;   7. We get all the values for q since we asked for it using run*.
;--------------------------------------------------------------------------------------
;Q3)
;;(run 1 (q)
;;  alwayso
;;  fail)

; ans: infinite loop
; reason:
;   1. alwayso is an infinite number of successes. Thus the goal 'fail' is evaluated and fails obviously.
;   2. This leads to try another success from alwayso. Again it succeeds and 'fail' is evaluated. A failure again.
;   3. Thus, as long as there are success goals in alwayso the run will try them hoping to come up with an answer for
;      q. But unfortunately alwayso has an infinite number of successes leading to an infinite loop.
;   4. We also see that the run value, i.e. 1, is irrelevant here except for 0, which for anything would produce ().
;--------------------------------------------------------------------------------------
;Q4)
;;(run 1 (q)
;;  fail
;;  alwayso)

; ans: ()
; reason:
;   1. The goal 'fail' fails. So why bother going further, just return with a failure, i.e. ().
;   2. Here too, we see that run value is irrelevant for the result.
;--------------------------------------------------------------------------------------
;Q5)
;;(run 2 (q)
;;  (conde
;;    [succeed] ; <----------- A
;;    [nevero])) ; <---------- B

; ans: infinite loop
; reason:
;   1. The goal A is irrelevant here as it succeeds anyway.
;   2. nevero is an infinite number of fails, but unknowingly run would try to fetch an answer
;      for q out of this infinitely many goals. Each goal keeps on failing and thus an infinite loop.
;--------------------------------------------------------------------------------------
;Q6)
;;(run* (q)
;;  (exist (a b c d) ; <----------------------- A
;;    (== `(,a ,b) `(,c (,a . ,d))) ; <-------- B
;;    (== `(,b ,c) `((,a) ,d)) ; <------------- C
;;    (== `(,a ,b ,c ,d) q))) ; <-------------- D

; ans: ((() (()) () ()))
; reason:
;   1. A introduces fresh variables a, b, c, and d.
;   2. B succeeds and ends with setting a and c to _.0 Then b to (_.0 . _.1) and d to _.1 
;   3. In C it tries to unify ((_.0 . _.1) _.0) with ((_.0) _.1). This succeeds only when
;      _.1 represents () and _.0 represents (), which would result in the unification of
;      ((()) ()) with ((()) ()). This obviously succeeds.
;   4. Thus after the first two unifications we get a, b, c, and d as,
;      () (() . ()) () ()
;   5. It is obvious that b reduces to (())
;   6. Thus in D we put all these into a list and unify it with q resulting q,
;      ( ( () (()) () () ) )
;--------------------------------------------------------------------------------------
   


;=================================================Part II==================================================
;;(define one-item
;;  (lambda (x s)
;;    (cond
;;      [(null? s) '()]
;;      [else (cons (cons x (car s))
;;              (one-item x (cdr s)))])))

(define one-itemo
  (lambda (x s out)
    (conde
      [(nullo s) (== out '())]
      [(exist (a d res c)
         (conso a d s)
         (conso x a c)
         (conso c res out)
         (one-itemo x d res))])))

;;(define assq
;;  (lambda (x ls)
;;    (cond
;;      [(null? ls) #f]
;;      [(eq? (car (car ls)) x) (car ls)]
;;      [else (assq x (cdr ls))])))

(define assqo
  (lambda (x ls out)
    (conde
      [(nullo ls) fail]
      [(exist (p c)
         (caro ls p)
         (caro p c)
         (eqo c x)) (caro ls out)]
      [(exist (d)
         (cdro ls d)
         (assqo x d out))])))

;--------------------------------------------------------------------------------------
; Test cases for one-itemo and assqo
;--------------------------------------------------------------------------------------
(printf "\n=================================================\nTests cases for one-itemo and assqo\n=================================================\n")

(test "one-itemo-1"
  (run* (q)
    (one-itemo 'a '(b c d) q))
  '(((a . b) (a . c) (a . d))))

(test "one-itemo-2"
  (run* (q)
    (one-itemo q '(b c d) '((a . b) (a . c) (a . d))))
  '(a))

(test "one-itemo-3"
  (run* (q)
    (one-itemo 'a q '((a . b) (a . c) (a . d))))
  '((b c d)))

(test "one-itemo-4"
  (run* (q)
    (one-itemo 'a '(b c d) `((a . b) . ,q)))
  '(((a . c) (a . d))))

(test "one-itemo-5"
  (run* (q)
    (one-itemo 'a '(b c d) '((a . b) (a . c) (a . d))))
  '(_.0))

(test "one-itemo-6"
  (run* (q)
    (one-itemo 'a `(b ,q d) '((a . b) (a . c) (a . d))))
  '(c))

(test "one-itemo-7"
  (run* (q)
    (exist (x y)
      (one-itemo x y '((a . b) (a . c) (a . d)))
      (== `(,x ,y) q)))
  '((a (b c d))))

(test "one-itemo-8"
  (run 6 (q)
       (exist (x y z)
         (one-itemo x y z)
         (== `(,x ,y ,z) q)))
  '((_.0 () ()) (_.0 (_.1) ((_.0 . _.1)))
    (_.0 (_.1 _.2) ((_.0 . _.1) (_.0 . _.2)))
    (_.0 (_.1 _.2 _.3) ((_.0 . _.1) (_.0 . _.2) (_.0 . _.3)))
    (_.0 (_.1 _.2 _.3 _.4) ((_.0 . _.1) (_.0 . _.2) (_.0 . _.3) (_.0 . _.4)))
    (_.0 (_.1 _.2 _.3 _.4 _.5) ((_.0 . _.1) (_.0 . _.2) (_.0 . _.3) (_.0 . _.4) (_.0 . _.5)))))



(test "assqo-1"
  (run* (q)
    (assqo 'x '() q))
  '())

(test "assqo-2"
  (run* (q)
    (assqo 'x '((x . 5)) q))
  '((x . 5)))

(test "assqo-3"
  (run* (q)
    (assqo 'x '((y . 6) (x . 5)) q))
  '((x . 5)))

(test "assqo-4"
  (run* (q)
    (assqo 'x '((x . 6) (x . 5)) q))
  '((x . 6) (x . 5)))

(test "assqo-5"
  (run* (q)
    (assqo 'x '((x . 5)) '(x . 5)))
  '(_.0))

(test "assqo-6"
  (run* (q)
    (assqo 'x '((x . 6) (x . 5)) '(x . 6)))
  '(_.0))

(test "assqo-7"
  (run* (q)
    (assqo 'x '((x . 6) (x . 5)) '(x . 5)))
  '(_.0))

(test "assqo-8"
  (run* (q)
    (assqo q '((x . 6) (x . 5)) '(x . 5)))
  '(x))

(test "assqo-9"
  (run* (q)
    (assqo 'x '((x . 6) . ,q) '(x . 6)))
  '(_.0))

(multi-test "assqo-10"
            (run 10 (q)
                 (assqo 'x q '(x . 5)))
            '(((x . 5) . _.0)
              (_.0 (x . 5) . _.1)
              (_.0 _.1 (x . 5) . _.2)
              (_.0 _.1 _.2 (x . 5) . _.3)
              (_.0 _.1 _.2 _.3 (x . 5) . _.4)
              (_.0 _.1 _.2 _.3 _.4 (x . 5) . _.5)
              (_.0 _.1 _.2 _.3 _.4 _.5 (x . 5) . _.6)
              (_.0 _.1 _.2 _.3 _.4 _.5 _.6 (x . 5) . _.7)
              (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 (x . 5) . _.8)
              (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 (x . 5) . _.9))
            '(((x . 5) . _.0)
              ((_.0 . _.1) (x . 5) . _.2)
              ((_.0 . _.1) (_.2 . _.3) (x . 5) . _.4)
              ((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (x . 5) . _.6)
              ((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7) (x . 5) . _.8)
              ((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7) (_.8 . _.9) (x . 5) . _.10)
              ((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7) (_.8 . _.9) (_.10 . _.11) (x . 5) . _.12)
              ((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7) (_.8 . _.9) (_.10 . _.11) (_.12 . _.13) (x . 5) . _.14)
              ((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7) (_.8 . _.9) (_.10 . _.11) (_.12 . _.13) (_.14 . _.15) (x . 5) . _.16)
              ((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7) (_.8 . _.9) (_.10 . _.11) (_.12 . _.13) (_.14 . _.15) (_.16 . _.17) (x . 5) . _.18)))

(multi-test "assqo-11"
            (run 10 (q)
                 (exist (x y z)
                   (assqo x y z)
                   (== `(,x ,y ,z) q)))
            '((_.0 ((_.0 . _.1) . _.2) (_.0 . _.1))
              (_.0 (_.1 (_.0 . _.2) . _.3) (_.0 . _.2))
              (_.0 (_.1 _.2 (_.0 . _.3) . _.4) (_.0 . _.3))
              (_.0 (_.1 _.2 _.3 (_.0 . _.4) . _.5) (_.0 . _.4))
              (_.0 (_.1 _.2 _.3 _.4 (_.0 . _.5) . _.6) (_.0 . _.5))
              (_.0 (_.1 _.2 _.3 _.4 _.5 (_.0 . _.6) . _.7) (_.0 . _.6))
              (_.0 (_.1 _.2 _.3 _.4 _.5 _.6 (_.0 . _.7) . _.8) (_.0 . _.7))
              (_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 (_.0 . _.8) . _.9) (_.0 . _.8))
              (_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 (_.0 . _.9) . _.10) (_.0 . _.9))
              (_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 (_.0 . _.10) . _.11) (_.0 . _.10)))
            '((_.0
               ((_.0 . _.1) . _.2)
               (_.0 . _.1))
              (_.0
               ((_.1 . _.2) (_.0 . _.3) . _.4)
               (_.0 . _.3))
              (_.0
               ((_.1 . _.2) (_.3 . _.4) (_.0 . _.5) . _.6)
               (_.0 . _.5))
              (_.0
               ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.0 . _.7) . _.8)
               (_.0 . _.7))
              (_.0
               ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.7 . _.8) (_.0 . _.9) . _.10)
               (_.0 . _.9))
              (_.0
               ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.7 . _.8) (_.9 . _.10) (_.0 . _.11) . _.12)
               (_.0 . _.11))
              (_.0
               ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.7 . _.8)
                (_.9 . _.10) (_.11 . _.12) (_.0 . _.13) . _.14)
               (_.0 . _.13))
              (_.0
               ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.7 . _.8) (_.9 . _.10) (_.11 . _.12) (_.13 . _.14) (_.0 . _.15) . _.16)
               (_.0 . _.15))
              (_.0
               ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.7 . _.8) (_.9 . _.10) (_.11 . _.12) (_.13 . _.14) (_.15 . _.16) (_.0 . _.17) . _.18)
               (_.0 . _.17))
              (_.0
               ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.7 . _.8) (_.9 . _.10) (_.11 . _.12) (_.13 . _.14) (_.15 . _.16) (_.17 . _.18) (_.0 . _.19) . _.20)
               (_.0 . _.19))))
