;; Kind of useless, but very nice. 
;; Both numbers are recursed alternatively
;; When right on reaches zero, recursion stops.
(define plus
  (trace-lambda plus (n m)
    (cond
      [(eq? m 0) n]
      [else (add1 (plus m (sub1 n)))])))
	  
;; The usual recursion on one number
 (define plus-usual
   (trace-lambda plus-usual (n m)
     (cond
       [(eq? m 0) n]
       [else (add1 (plus (sub1 n) m))])))