(define alpha-subst
  (lambda (old new e)
    (pmatch e
      [(lambda (,x) ,body) ...]
      [,x (error 'alpha-subst "Invalid input: ~s" e)])))

(define alpha-subst-helper
  (lambda (old new e)
    (pmatch e
      [,x (guard (symbol? x)) ...]
      [(lambda (,x) ,body) 
       (if (and (free? x body) 
       ]
      [(,rator ,rand) ...])))

(define free?
 (lambda (y e)
   (pmatch e
     [,x (guard(symbol? x)) (eq? x y)]
     [(lambda(,x) ,m) (and (not (eq? x y)) (free? y m))]
     [(,rator ,rand) (or (free? y rator) (free? y rand))])))
            