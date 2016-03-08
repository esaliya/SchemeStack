;;-----------------------
;; Saliya Ekanayake
;; sekanaya
;; Test15
;;-----------------------

;; CPS style factorial
(letrec ([fact-cps (lambda (n k)
                     (if (eq? n 0)
                         (k 1)
                         (fact-cps (- n 1) (lambda (v) (k (* n v))))))])
  (fact-cps 5 (lambda (k) k)))