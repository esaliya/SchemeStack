

(define valof 
  (lambda (exp env)
    (pmatch exp
      (,x (guard (symbol? x)) (env x))
      ((lambda (,x) ,body) (lambda (a) (valof body (lambda (y) (if (eq? x y) a (env y))))))
      ((,rator ,rand) ((valof rator env) (valof rand env))))))
;CPS interpreter
;lambda's as values require k to be applied to it
;lambda's as arguements don't
;'--' means that where continuations need to be made rep independent
(define valof 
  (lambda (exp env k) 
    (pmatch exp
      (,x (guard (symbol? x)) (env x k)) ;(k (env x)) also works but supposedly is harder later -- no continuation issues here; none made or applied
      ((lambda (,x) ,body) (k (lambda (a k) (valof body (lambda (y k) (if (eq? x y) (k a) (env y k)))k)))) ; (k (lam... and (k a)
      ((,rator ,rand) ((valof rand env (lambda (a) (valof rator env (lambda (p) (p a k)))))))))) ;building 2 continuations (lambda (a) (... and (lambda (p) (...
(valof '(__expr__) (lambda (y) 'error) (lambda (x) x)) ; -- (lambda (x) x)

;proc rep
(define apply-k
  (lambda (k v)
    (k v)))
;proc rep
(define extend-p/k
  (lambda (a k))
    (lambda (p) (p a k)))
;proc rep
(define extend-a/k
  (lambda (rator env k))
    (lambda (a) (valof rator env (extend-p/k a k))))
;proc rep
(define empty-k
  (lambda ()
    (lambda (x) x)))
;proc rep
(define valof 
  (lambda (exp env k) 
    (pmatch exp
      (,x (guard (symbol? x)) (env x k)) ;(k (env x)) also works but supposedly is harder later -- no continuation issues here; none made or applied
      ((lambda (,x) ,body) (apply-k k (lambda (a k) (valof body (lambda (y k) (if (eq? x y) (apply-k k a) (env y k)))k)))) ; (k (lam... and (k a)
      ((,rator ,rand) ((valof rand env (extend-a/k rator env k))))))) ;building 2 continuations (lambda (a) (... and (lambda (p) (...
(valof '(__expr__) (lambda (y) 'error) (empty-k)) ; -- (lambda (x) x)

;Data Structure Representations of the representation functions
;data rep
(define empty-k
  (lambda ()
    ('(empty-k))))
;data rep
(define extend-a/k
  (lambda (rator env k)
    `(extend-a/k ,rator ,env ,k)))
;data rep
(define extend-p/k
  (lambda (a k)
    `(extend-p/k ,a ,k)))
;data rep
(define apply-k
  (lambda k v)
    (pmatch k
      ((mt-k) v) ;or (let ((x v)) x)
      ((extend-a/k ,rator ,env ,k) (valof rator env (extend-p/k v k));or (let ((a v)) (valof rator env (extend-p/k a k)))
      ((extend-p/k ,a ,k) (v a k))))) ; (let ((p a)) (p a k))

(call/cc f)
  (lambda (k) .. (k 4) ..)


friendlier version
  (letcc k ...) (throw expi k-exp) ;--throw the value exp to the continuation k-exp

  [(letcc ,x ,body (call/cc (lambda (k) (valof body (extent-env x k env)))))]
  ;If we were nervous --> (guard (symbol? x))
  ;k would represent on of schemes continuations

  [(throw ,exp ,k-exp) ((valof k-exp env)(valof exp env))] 

(valof '(+ 3 (letcc k (+ 4 (throw 5 k))) (empty-env))
;continguation is add 3
;k=(lambda-hat (v) (+ 3 v));;tail possition lambda
;throw valof 5-> and k-> to the above 
;returns 5

;cps interp
(define valof
  (lambda (exp env k)

   ((letcc ,x ,body) (valof body (entend-env x k env) k))
   ((throw ,exp ,k-exp) ((valof k-exp env 
                          (lambda (c) (valof exp env 
                                        (lambda (a) (c a)))))))
   ;since (lambda (a) (c a)) is eta then it is the same a c
   ((throw ,exp ,k-exp) ((valof k-exp env 
                          (lambda (c) (valof exp env c)))))


or use a callcc
  ((call/cc rator) (valof rator env (lambda (p) (p (lambda (a k-hat) (k a)) k))))
  ;;(lambda (a k-hat) (k a)) lets us essentially drop the current continuation (k-hat) and use k



