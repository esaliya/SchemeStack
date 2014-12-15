; This is using built in boxes
(define calee
  (lambda (x-box)
    (printf "\ncalee original val ~s" (unbox x-box))
    (set-box! x-box 4)
    (printf "\ncalee val after set-box! ~s" (unbox x-box))))

(define caller
  (lambda ()
    (let ([p-box (box 7)])
      (printf "\ncaller original val ~s" (unbox p-box))
      (calee p-box)
      (printf "\ncaller val after calee ~s" (unbox p-box)))))


; Now with my own version of boxes
(define calee-my
  (lambda (x-box)
    (printf "\ncalee original val ~s" (car x-box))
    (set-car! x-box 4)
    (printf "\ncalee val after set-box! ~s" (car x-box))))

(define caller-my
  (lambda ()
    (let ([p-box (cons 7 '())])
      (printf "\ncaller original val ~s" (car p-box))
      (calee-my p-box)
      (printf "\ncaller val after calee ~s" (car p-box)))))