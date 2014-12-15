;; the idea is you should be able to set the state of some variable
;; within the environment created in the lambda case. Since doing a set! 
;; to any variable declared within that env has no use, we will set! 
;; a useless varialble outside (free) the env. 

;; since x in (lambda (,x) ...) is local to the particular step in the recursion
;; we can safely set! this. So we will check,
;; 1.) if x == x^ for the first time. we determine if it's first time by checking if x is a symbol
;;     if so we will set! x to a pair. The car is the symbol captured by x. cdr is the value of a wrapped in a thunk
;; 2.) if x == x^ given we have done 1.) already. We know we've done 1.) already if x is a pair
;;     then there's nothing to take the value of a because we have already stored its value in the cdr in a thunk.
;;     so return it
;; 3.) else as usual check in old env

define vof
  (trace-lambda vof (e env)
    (pmatch e
      [,x (guard (symbol? x)) ((env x))]
	  [,n (guard (number? n)) n]
	  [(+ ,n1 ,n2) (+ (vof n1 env) (vof n2 env))]
	  [(lambda (,x) ,body) (lambda (a) (vof body (lambda (x^) 
	                                               (cond
												     [(and (symbol? x) (eq? x x^)) (begin (set! x (cons x (let ([a (a)]) (lambda () a)))) (cdr x))]
													 [(and (pair? x) (eq? (car x) x^)) (cdr x)]
													 [else (env x^)]))))]
	                                               
												       
	  [(,rator ,x) (guard (symbol? x)) ((vof rator env) (env x))]
	  [(,rator , rand) ((vof rator env) (lambda () (vof rand env)))])))
	  
;; to check run the following
;; (vof '((lambda (x) (+ x x)) 2) (lambda(x) (error 'mtevn "error")))

;; you should get 
;;|(vof ((lambda (x) (+ x x)) 2) #<procedure>)
;;| (vof (lambda (x) (+ x x)) #<procedure>)
;;| #<procedure>
;;|(vof (+ x x) #<procedure>)
;;| (vof x #<procedure>)
;;| |(vof 2 #<procedure>)
;;| |2
;;| 2
;;| (vof x #<procedure>)
;;| 2
;;|4
;;4

;; where only ONE call to (vof 2 #<procedure>) is made.