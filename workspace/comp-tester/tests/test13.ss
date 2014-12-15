;;-----------------------
;; Saliya Ekanayake
;; sekanaya
;; Test13
;;-----------------------

;; Factorial 5 with anonymous lambda
(((lambda (fac.1)
    (fac.1 fac.1))
  (lambda (fac.2)
    (lambda (n.3)
      (if (eq? n.3 '0) '1
          (* ((fac.2 fac.2) (- n.3 '1)) n.3))))) '5)