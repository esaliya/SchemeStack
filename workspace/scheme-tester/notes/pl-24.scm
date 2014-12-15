
 ;logic programming
;miniKanren
; run                  run*      interface
 
; ---
; ---                  (==)      unification
; ---
 
; exist                exist     sequencing / introduce variable
; cond superscript e   (code)    nondeterministic choice (dan doesn't like that name)

;unification examples
(== 5 5)  ;succeeds or fails -- can bind a variable
(== 5 6)  ;fail
(== 5 x)  ;depends if x is bound; if it is not succeeds and x becomes 5
(== x y)  ;if one is unbound the other is bound, if neither is bound then they become connected -- same var
(== `(,x . ,x) `(5 . 6)) ;fails x can't be 5 and 6

;introduing variables (declaring)
(exist (varialbe-list) body)
(exist (x y z) 
  (== `(,x . ,x) `(,y . ,z))
  (== y 5))
; order of expressions does not matter
; logic programming principle: try to fail fast -- otherwise infinite loops may occur
; succeed will always succeed regardless of ordering
; fail may diverge and never end with reordering
;similar to AND but returning succeed or fail not #t or #f

(run* (run-variable) body body*)
(run* (x) 
  (== 5 x))
(5)

(run* (q)
  (exist (x y)
    (== x 5)
    (== y 6)
    (== `(,x ,y) q)))
((5 6))


(run* (q)
  (exist (x y)
    (== x 5)
    (== x #t)
    (== y 6)
    (== `(,x ,y) q)))
()


(run* (q)
  (conde
    ((== q 5))
    ((== q 6))))
(5 6)

;(run 1 -- return 1 answers -- not nessassary the number of conde clauses)
;(run X -- return X answers)
>(load "mkdefs.scm")
>(run* (q) (==q 5))
(5)
(run* (q) (== 5 5)) ; only 1 conde test so only 1 value is contributed -- reserved value _.# is used meaning unbound
(_.0) ;variable 0

(run* (q)
  (exist (x y z)
    (conde
      ((== 5 5))
      ((== 6 6)))
    (== `(,x ,y ,z ,x) q)))
((_.0 _.1 _.2 _.0))
      
;make a minikanran program -- first add an 'o' at the end of the name
;append -> appendo

(define append
  (lambda (l s)
    (cond 
      ((null? l) s)
      (else (cons (car l) (append (cdr l) s))))))


(define appendo
  (lambda (l s out)
    (conde 
      ((== '() l) (== out s))
      ((exist (a d res)
        (== `(,a . ,d) l) ;else of null? could be anything, this ensures that it is a pair  
        (== `(,a . ,res) out) ;cps like -- not sure why
        (appendo d s res)))))) ;recursive call at the bottom (exists clauses are executed top down; conde can be any order)
 
 (run* (q) (appendo  q '(d e) '(a b c d e)))
 ((a b c))

;Day 2
(run* (q)
  (exist (x)
   (== `(x) x)))
(_.0)
;BUT
(run* (q)
   (== `(,q) q))
;will not terminate since run can't print out an inf list

;Sound Unification -- ensures that no recurisive 
(==-check

;anyo (seen in the hwk) -- diverges for run* but not for runk (since the k keeps it from recursing forever)
;metaphorically constructing a nested conde recursively

;conde calls each clause in a trampoline like fashion

;alwayso 
;same as anyo with succeed

;A goal takes in a substition and returns

(run 1 (x)
  (== #t x)
  alwayso
  (== #f x))
;infinite number of success followed by a failure causes infinite loop
;since the fail alway goes back to upper goals to get another value
(run 1 (x)
  (== #t x)
  (== #f x)
  alwayso) ;WILL WORK -- ()

;nevero: anyo of fail

(run 1 (q) nevero) ;-- diverge -- like a conde with infinite number of failing clauses

(run 3 (q)
  (conde
    ((== q 1))
    (nevero)
    (conde
      ((== q 2))
      (nevero)
      ((== q 3)))))
(1 2 3) ; since conde allows us to trampoline over the nevero inf loop; if it was run 4 then we would diverge

miniKanren version of the value-of functions
;1. Prepwork
;tagged list representation on an interpreter allows unificaiton to be used in a miniKanren version
;like (var x) instead of x and (int 2) instead of 2
;also rep ind of closures and environments
;2. rename to value-ofo and create an output argument
;3. change pmantch to conde expression
;   like 
(pmatch expr
  ((var ,x) (apply-env env x)))
  to
(cond
  ((== `(var ,x)) (apply-env env x)))
;all the the expressions of conde will have tags to match against (var, int ,sub1, zero...)
;3b.. (,rand ,rator) -- does not have this format SO add the and app tag like (app ,rand ,rator)
;4. upate test procedure such that tagged notiations are updated
;5. make returns unifications with out like  n) =>> (== n out)
;6. decide what functions are serious (the ones that need to be 'o' functions): apply-envo apply-proco (change to the cps like style)
;7. update helpers (apply-envo -> pmatch to conde and if to conde) and error calls go to fails: (== #t #f) or remove line entirely
