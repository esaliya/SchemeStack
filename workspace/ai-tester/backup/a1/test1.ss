(define blank 'blank)
(define test-goal (make-goal-state 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23
                                   24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43
                                   44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63
                                   blank))

(define test-case-1 (make-initial-state 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23
                                   24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43
                                   44 45 blank 46 47 49 50 51 52 53 54 55 48 57 58 59 60 61 62
                                   63 56))

;;(test-uninformed-search init test-goal 20000)

;;(let gen ([s '()] [i 64])
;;  (if  (> i 0)
;;      (gen (cons i s) (sub1 i))
;;      s))