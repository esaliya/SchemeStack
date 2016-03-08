;;-----------------------
;; Saliya Ekanayake
;; sekanaya
;; Test13
;;-----------------------

; Tests mutation with pair and variable
(let ([x.1 '(9)][x.2 7])
  (let ([y.3 x.1] [y.4 x.2])
    (begin
      (set-car! x.1 x.2)
      (set! x.2 8)
      (cons x.1 (cons x.2 (cons y.3 (cons y.4 '())))))))