;; a12 - introduce-procedure-primitives
;; ------------------------------------
;; My implementation depends on the fact that
;; each application will get rator's closure
;; pointer as the first rand. This may not
;; be the case after some optimization pass.
;; So at that point handle it.
;; 
;; Also will have to change
 define (Lambda lamb)
    (match lamb
      [(lambda (,cp ,uvar* ...) (bind-free (,cp ,f* ...) ,ex))
       (let ([ex ((Expr cp f*) ex)])
         `(lambda (,cp ,uvar* ...) ,ex))]
      [,x (error who "invalid Lambda ~s" x)]))
 


;; Remove items from S if they are in L too
;; This is basically set difference. Also it
;; depends on the eq check since it uses remq
;; So may not work with nested lists. If necessary
;; change it to remove
 (define remove-items
    (lambda (s l)
      (cond 
        [(or (null? s) (null? l)) s]
        [else (remove-items (remq (car l) s) (cdr l))])))