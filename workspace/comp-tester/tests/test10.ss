; Saliya Ekanayake
; sekanaya
; Test 10

; Calculates how many cons operations are necessary to
; create the given list
(letrec ([cons-cell-count$1 
          (lambda (p.2)
            (if (pair? p.2)
                (+ '1 (+ (cons-cell-count$1 (car p.2)) (cons-cell-count$1 (cdr p.2))))
                '0))])
  (begin
    (let ([p.1 (cons '3 (cons '1 (cons '2 '())))])
      (cons-cell-count$1 p.1))))
      