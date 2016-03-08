(value-of
   '(natrec 
     (succ zero) 
     (zero (succ zero)) 
     (succ _ with y (succ y)))
   (empty-env))