; if we can give the factorial function to the following function then we can compute factorials

(lambda (!)
  (lambda (n)
    (if (zero? n)
      1
      (* n (! (sub1 n))))))

; this will be Y and the input will be the function define above and will output a factorial function

(((lambda (r)
    ((lambda (f)
      (f f) (lambda (f)
              )))
      
   
   
    ) (lambda (!)
       (lambda (n)
         (if (zero? n)
           1
           (* n (! (sub1 n))))))
  ) 5)


;---------------
(define fact-gen 
  (lambda (fact-in)
     (lambda (n)
       (if (zero? n) 1
         (* n (fact-in (- n 1)))))))