;;-----------------------
;; Saliya Ekanayake
;; sekanaya
;; Test8
;;-----------------------

;; Adds the elements of an array by going through each element.
;; The strategy is to set the element at p.2 + (c.3-1) * 8 to the 
;; addition of itself with element at p.2 + c.3 * 8. It will return
;; the value at p.2 + c.3 * 8 when c.3 is equal to zero. In essence
;; this adds an array from tail to head.
(letrec ([f$0 (lambda (p.2 c.3) (locals () 
                                  (if (> c.3 0)
                                      (begin
                                        (mset! p.2 (* (- c.3 1) 8) (+ (mref p.2 (* c.3 8)) (mref p.2 (* (- c.3 1) 8))))
                                        (f$0 p.2 (- c.3 1)))
                                      (mref p.2 c.3))))])
  (locals (x.1)
    (begin
      (set! x.1 (alloc 24))
      (mset! x.1 0 10)
      (mset! x.1 8 15)
      (mset! x.1 16 20)
      (f$0 x.1 2))))