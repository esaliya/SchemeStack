;;-----------------------
;; Saliya Ekanayake
;; sekanaya
;; Test7
;;-----------------------

;; Aha! finally the much awaited form of Scheme :)
;; and the usual factorial calculator
(letrec ([fac$1 (lambda (x.1) 
                  (locals () 
                    (if (= x.1 0) 
                        x.1 
                        (* x.1 (fac$1 (- x.1 1))))))])
  (locals () (fac$1 5)))