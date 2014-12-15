;;-----------------------
;; Saliya Ekanayake
;; sekanaya
;; Test11
;;-----------------------

; Finds the number of occurences of x.2 in p.1
(let ([p.1 (cons '#t (cons '#t (cons '#f (cons '#t '()))))] [x.2 '#t])
  (letrec ([num-occurs$1 (lambda (p.3 x.4)
                           (if (null? p.3)
                               '0
                               (if (eq? (car p.3) x.4)
                                   (+ '1 (num-occurs$1 (cdr p.3) x.4))
                                   (if (pair? (car p.3))
                                       (+ (num-occurs$1 (car p.3) x.4)
                                          (num-occurs$1 (cdr p.3) x.4))
                                       (num-occurs$1 (cdr p.3) x.4)))))])
    (num-occurs$1 p.1 x.2)))
                                              
                           