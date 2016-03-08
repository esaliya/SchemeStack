

;----------------------------------------------------------------
; Questions on run interface
;----------------------------------------------------------------

;----------------------------------------------------------------
;Q1)

(run* (q)
  (== 5 5)
  (== 6 6))
;ans: (_.0)

(run* (q)
  (conde
    [(== 5 5)]
    [(== 6 6)]))
;ans: (_.0 _.0) <-- why two values for this case?
;----------------------------------------------------------------


;----------------------------------------------------------------
;Q2)

;;(define succeed (== #f #f))
;;(define fail (== #f #t))
;; 
;;(define anyo
;;  (lambda (g)
;;    (conde
;;      [g]
;;      [(anyo g)])))
;; 
;;(define alwayso (anyo succeed))
;;(define nevero (anyo fail))

(run 1 (q)
    alwayso)
;ans: (_.0) <-- why not infinite loop?

(run 1 (x)
  (== #t x)
  alwayso
  (== #f x))
;ans: infinite <-- why?

(run 1 (x)
  (== #t x)
  (== #f x)
  alwayso)
; ans: () <-- why not infinite loop?


;----------------------------------------------------------------
;Q3)

(run* (q)  
  (exist (x y)
    (conde
      [(== x 5) (== q 6)]
      [(== y 7) (== q 9)])))
;ans: (6 9)

(run* (q)  
  (exist (x y)
    (conde
      [(== x 5) (== q 6)]
      [(== y 7) (== q 9)]))
  (== q 6))
;ans: (6) <-- why no 9 now?

(run* (q)  
  (exist (x y)
    (conde
      [(== x 5) (== y 6)]
      [(== y 7) (== x 9)]))
  (== q 6))
;ans: (6 6) <-- why two 6 now?

;----------------------------------------------------------------
;Q4)

(run* (q)
   (== `(,q) q))


