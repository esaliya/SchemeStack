; Saliya Ekanayake
; sekanaya
; Test 6
(letrec ([f$1 (lambda (x.1 y.2)
                (locals ()
                  (if (< x.1 y.2)
                      (+ x.1 y.2)
                      (f$2 (- x.1 y.2)))))]
         [f$2 (lambda (z.3)
                (locals (a.4)
                  (begin
                    (set! a.4 10)
                    (+ a.4 z.3))))])
  (locals ()
    (f$1 20 20)))
               