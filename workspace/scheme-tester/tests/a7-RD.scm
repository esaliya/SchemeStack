(define value-of
  (lambda (exp env k)
    (pmatch exp
      ; we want to do (k (env x)), but to make it tail form we do (env x k)
      [,x (guard (symbol? x)) (env x k)]
      [,n (guard (or (number? n) (boolean? n))) (k n)]
      [(+ ,x1 ,x2) (value-of x1 env (lambda (v) (value-of x2 env (lambda (w) (k (+ v w))))))]
      [(call/cc ,rator) (value-of rator env (lambda (p) (p (lambda (a k^) (k a)) k)))] 
      [(lambda (,x) ,body) (k (lambda (a c) (value-of body 
                                                      (lambda (y t) (if (eq? x y) (t a) (env y t))) 
                                                      c)))]
      [(,rator ,rand) (value-of rand env (lambda (v) (value-of rator env (lambda (p) (p v k)))))])))

(define empty-env
  (lambda ()
    (lambda (y k)
      (error 'mt-env "unbound variable ~s : discontinuing contination" y))))

(define empty-k
  (lambda ()
    (lambda (x) x)))