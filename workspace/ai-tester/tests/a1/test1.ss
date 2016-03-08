;; Test cases for 8-puzzle search
;; Relies on "make-goal-state" and "make-initial-state" functions, so
;; you should load your scheme file first and then this one.
;; 
;; You can either use the test cases individually, or they're arranged
;; into lists by group - you can "eval" each item in the list in turn
;; and invoke your search function on the eval'd state.
;; 
;; The depth limits given are for optimal paths (such as you would get
;; with breadth-first search but not necessarily depth-first) and are
;; theoretical upper limits -- since the board is shuffled randomly,
;; the actual optimal depth may be much less than indicated.

(define blank 'blank)
(define test-goal (make-goal-state 1 2 3 4 5 6 7 8 blank))

;; First group of test cases - should have solutions with depth <= 5
(define test-case-1 (make-initial-state 2 blank 3 1 5 6 4 7 8))
(define test-case-2 (make-initial-state 1 2 3 blank 4 6 7 5 8))
(define test-case-3 (make-initial-state 1 2 3 4 5 6 7 blank 8))
(define test-case-4 (make-initial-state 1 blank 3 5 2 6 4 7 8))
(define test-case-5 (make-initial-state 1 2 3 4 8 5 7 blank 6))
(define test-group-1 `(,(make-initial-state 2 blank 3 1 5 6 4 7 8)
                       ,(make-initial-state 1 2 3 blank 4 6 7 5 8)
                       ,(make-initial-state 1 2 3 4 5 6 7 blank 8)
                       ,(make-initial-state 1 blank 3 5 2 6 4 7 8)
                       ,(make-initial-state 1 2 3 4 8 5 7 blank 6)))


;; Second group of test cases - should have solutions with depth <= 10
(define test-case-6 (make-initial-state 2 8 3 1 blank 5 4 7 6))
(define test-case-7 (make-initial-state 1 2 3 4 5 6 blank 7 8))
(define test-case-8 (make-initial-state blank 2 3 1 5 6 4 7 8))
(define test-case-9 (make-initial-state 1 3 blank 4 2 6 7 5 8))
(define test-case-10 (make-initial-state 1 3 blank 4 2 5 7 8 6))
(define test-group-2 `(,(make-initial-state 2 8 3 1 blank 5 4 7 6)
                       ,(make-initial-state 1 2 3 4 5 6 blank 7 8)
                       ,(make-initial-state blank 2 3 1 5 6 4 7 8)
                       ,(make-initial-state 1 3 blank 4 2 6 7 5 8)
                       ,(make-initial-state 1 3 blank 4 2 5 7 8 6)))

;; Third group of test cases - should have solutions with depth <= 20
(define test-case-11 (make-initial-state blank 5 3 2 1 6 4 7 8))
(define test-case-12 (make-initial-state 5 1 3 2 blank 6 4 7 8))
(define test-case-13 (make-initial-state 2 3 8 1 6 5 4 7 blank))
(define test-case-14 (make-initial-state 1 2 3 5 blank 6 4 7 8))
(define test-case-15 (make-initial-state blank 3 6 2 1 5 4 7 8))
(define test-group-3 `(,(make-initial-state blank 5 3 2 1 6 4 7 8)
                       ,(make-initial-state 5 1 3 2 blank 6 4 7 8)
                       ,(make-initial-state 2 3 8 1 6 5 4 7 blank)
                       ,(make-initial-state 1 2 3 5 blank 6 4 7 8)
                       ,(make-initial-state blank 3 6 2 1 5 4 7 8)))

;; Fourth group of test cases - should have solutions with depth <= 50
(define test-case-16 (make-initial-state 2 6 5 4 blank 3 7 1 8))
(define test-case-17 (make-initial-state 3 6 blank 5 7 8 2 1 4))
(define test-case-18 (make-initial-state 1 5 blank 2 3 8 4 6 7))
(define test-case-19 (make-initial-state 2 5 3 4 blank 8 6 1 7))
(define test-case-20 (make-initial-state 3 8 5 1 6 7 4 2 blank))
(define test-group-4 `(,(make-initial-state 2 6 5 4 blank 3 7 1 8)
                       ,(make-initial-state 3 6 blank 5 7 8 2 1 4)
                       ,(make-initial-state 1 5 blank 2 3 8 4 6 7)
                       ,(make-initial-state 2 5 3 4 blank 8 6 1 7)
                       ,(make-initial-state 3 8 5 1 6 7 4 2 blank)))
(define test-group-all `(,@test-group-1 ,@test-group-2 ,@test-group-3 ,@test-group-4))

;;(for-each (lambda (init) (test-uninformed-search init test-goal 20000)) test-group-1)