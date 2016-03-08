; Saliya Ekanayake
; sekanaya
; Assignment 4

;; returns true iff triv is either register or uvar
(define uvar-or-reg?
  (lambda (triv)
    (or (register? triv) (uvar? triv))))

;; returns a sub set of items which satisfies the 
;; predicate from the given set, l
(define select
  (lambda (l predicate?)
    (match l
      [() '()]
      [(,item . ,[l]) (if (predicate? item) `(,item . ,l) l)])))
 

;---------------------------------------------------------------
; Pass:           
;   uncover-register-conflicts
;
; Description: 
;   Relies on the output of verify-scheme pass and
;   discovers register conflicts. It returns the 
;   conflict graph along with rest of the code
;   in accordance with the output grammar.
;
; Input Language:  
;   Program	    -->	(letrec ([label (lambda () Body)]*) Body)
;   Body	    -->	(locals (uvar*) Tail)
;   Tail	    -->	(Triv Loc*)
;	             |	(if Pred Tail Tail)
;         	     |	(begin Effect* Tail)
;   Pred    	-->	(true)
;           	 |	(false)
;           	 |	(relop Triv Triv)
;           	 |	(if Pred Pred Pred)
;    	         |	(begin Effect* Pred)
;   Effect	-->	(nop)
;           	 |	(set! Var Triv)
;	             |	(set! Var (binop Triv Triv))
;           	 |	(if Pred Effect Effect)
;	             |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    	-->	Var | int | label
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body	-->	(locals (uvar*)
;               (register-conflict conflict-graph Tail))
;   Tail	-->	(Triv Loc*)
;	         |	(if Pred Tail Tail)
;   	     |	(begin Effect* Tail)
;   Pred	-->	(true)
;	         |	(false)
;	         |	(relop Triv Triv)
;            |	(if Pred Pred Pred)
;            |	(begin Effect* Pred)
;   Effect	-->	(nop)
;	         |	(set! Var Triv)
;            |	(set! Var (binop Triv Triv))
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv	-->	Var | int | label
;---------------------------------------------------------------


(define-who uncover-register-conflict
 (define handle-assignment!
    (lambda (var liveset alist)
      (cond
       [(register? var)
        (set-conflicts! (select liveset uvar?) alist var)]
       [(uvar? var)
        (let ([row (assq var alist)])
          (set-cdr! row (union liveset (cdr row)))
          (set-conflicts! (select liveset uvar?) alist var))])))
  (define set-conflicts!
    (lambda (ulist alist var)
      (if (not (null? ulist))
          (let ([row (assq (car ulist) alist)])
            (set-cdr! row (union `(,var) (cdr row)))
            (set-conflicts! (cdr ulist) alist var)))))
  (define Tail
    (lambda (tail alist liveset)
      (match tail
        [(if ,pred ,[trueset] ,[falseset]) (Pred pred alist trueset falseset)]
        [(begin ,ef* ... ,[tailset]) (Effect* ef* alist tailset)] 
        [(,triv ,loc* ...) (union liveset (select `(,triv) uvar-or-reg?) loc*)])))
  (define Pred
    (lambda (pred alist trueset falseset)
      (match pred
        [(true) trueset]
        [(false) falseset]
        [(begin ,ef* ... ,[predset]) (Effect* ef* alist predset)]
        [(if ,pred ,[trueset] ,[falseset]) (Pred pred alist trueset falseset)]
        [(,relop ,triv1 ,triv2) 
         (union trueset falseset (select `(,triv1 ,triv2) uvar-or-reg?))])))
  (define Effect*
    (lambda (ef* alist liveset)
      (match ef*
        [() liveset]
        [(,x* ... (nop)) (Effect* x* alist liveset)]
        [(,x* ... (if ,pred ,ef1 ,ef2))
         (let* ([trueset (Effect* `(,ef1) alist liveset)]
                [falseset (Effect* `(,ef2) alist liveset)]
                [predset (Pred pred alist trueset falseset)])
           (Effect* x* alist predset))]
        [(,x* ... (begin ,ef* ...)) 
         (Effect* `(,x* ... ,ef* ...) alist liveset)]
        [(,x* ... (set! ,var (,binop ,var ,triv)))
         (let ([liveset (remq var liveset)])
           (handle-assignment! var liveset alist)
           (Effect* x* alist (union liveset (select `(,var ,triv) uvar-or-reg?))))]
        [(,x* ... (set! ,var ,triv)) 
         (let ([liveset (remq var liveset)])
           (handle-assignment! var (remq triv liveset) alist)
           (Effect* x* alist (union liveset (select `(,triv) uvar-or-reg?))))])))
  (define Body
    (lambda (body)
      (match body
        [(locals (,uvar* ...) ,tail)
         (let([alist `((,uvar*) ...)])
           (Tail tail alist '()) ; neglect the returned liveset
           `(locals (,uvar* ...) (register-conflict ,alist ,tail)))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   assign-registers
;
; Description: 
;   Relies on the output of uncover-register-conflicts.
;   This tries to assign registers to uvars based 
;   on the conflict graph. If it is unable to assign
;   registers to all the uvars it gives an error containing
;   the spilled variabled.
;
; Input Language:  
;   Same as the output from uncover-register-conflict 
;
; Output Language: 

;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body	-->	(locate ([uvar reg]*) Tail)
;   Tail	-->	(Triv Loc*)
;	         |	(if Pred Tail Tail)
;            |	(begin Effect* Tail)
;   Pred	-->	(true)
;	         |	(false)
;            |	(relop Triv Triv)
;	         |	(if Pred Pred Pred)
;	         |	(begin Effect* Pred)
;   Effect	-->	(nop)
;	         |	(set! Var Triv)
;	         |	(set! Var (binop Triv Triv))
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv	-->	Var | int | label
;---------------------------------------------------------------
(define-who assign-registers
  (define picklow
    (lambda (cg)
      (cond
       [(null? cg) #f]
       [(< (sub1 (length (car cg))) (length registers)) (car cg)]
       [else (picklow (cdr cg))])))
  (define remove
    (lambda (cg pick)
      (map (lambda (row)
             (cons (car row) (remq (car pick) (cdr row)))) (remq pick cg))))
  (define pick-and-remove
    (lambda (cg)
      (if (not (null? cg))
          (let ([pick (or (picklow cg) (car cg))])
            (values pick (remove cg pick)))
          (values '() '()))))
  (define simplify
    (lambda (uvar* cg)
      (if (null? uvar*)
          (values '() '()) ; if uvar* is null no assignments & spills
          (let*-values
              ([(pick cg) (pick-and-remove cg)] ; picked row and modifief cg 
               [(alist spills) (simplify (remq (car pick) uvar*) cg)]
               [(pickregs) (select (cdr pick) register?)] ; registers in picked row
               [(otherregs) (remq #f (map
                                      (lambda (uvar)
                                        (let ([p (assq uvar alist)])
                                          (if p
                                              (cadr p)
                                              #f)))
                                      (difference (cdr pick) pickregs)))]
               [(availregs) (difference registers (union pickregs otherregs))])
            (if (not (null? availregs))
                (values
                  (cons `(,(car pick) ,(car availregs)) alist)
                  spills)
                (values alist (cons (car pick) spills)))))))
  (define handle-allocation
    (lambda (uvar* cg)
      (let-values ([(alist spills) (simplify uvar* cg)])
        (if (null? spills)
            alist
            (error who "spills found ~s" spills)))))
  (define Body
    (lambda (body)
      (match body
        [(locals (,uvar* ...) (register-conflict ,cg ,tail))
         `(locate ,(handle-allocation uvar* cg) ,tail)]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   discard-call-live
;
; Description: 
;   Relies on the output of assign-registers.
;   This discards the Loc* in tail calls. It 
;   keeps the rest as it is.
;
; Input Language:  
;   Same as the output from assign-registers 
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body	-->	(locate ([uvar reg]*) Tail)
;   Tail	-->	(Triv)
;	         |	(if Pred Tail Tail)
;            |	(begin Effect* Tail)
;   Pred	-->	(true)
;            |	(false)
;            |	(relop Triv Triv)
;	         |	(if Pred Pred Pred)
;	         |	(begin Effect* Pred)
;   Effect	-->	(nop)
;	         |	(set! Var Triv)
;            |	(set! Var (binop Triv Triv))
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;   Loc   	-->	reg | fvar
;   Var   	-->	uvar | Loc
;   Triv	-->	Var | int | label
;---------------------------------------------------------------
(define-who discard-call-live
  (define Tail
    (lambda (tail)
      (match tail
        [(if ,pred ,[ttail] ,[ftail]) `(if ,pred ,ttail ,ftail)]
        [(begin ,ef* ... ,[tail]) `(begin ,ef* ... ,tail)] 
        [(,triv ,loc* ...) `(,triv)])))
  (define Body
    (lambda (body)
      (match body
        [(locate ([,uvar* ,reg*] ...) ,[Tail -> tail])
         `(locate ([,uvar* ,reg*] ...) ,tail)]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------





       