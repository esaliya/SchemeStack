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

;---------------------------------------------------------------
; Pass:           
;   expose-basic-blocks
;
; Description: 
;   Relies on the output of expose-frame-var pass. The idea
;   of this pass is to create basic blocks for each "then",
;   "else", and "join" parts, which results due to branching
;   operation of "if". These sequential blocks are pushed to
;   to the top as thunks. In the output language branching
;   happens with conditional jumps based on the simpler form
;   of (if (relop triv triv) (clab) (flab)). All these simple
;   "if" forms appear only in the tail position of the blocks.
;
; Input Language:  
;   Same as the output language of expose-frame-var 
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Tail)]*) Tail)
;   Tail	-->	(Triv)
;	         |	(if (relop Triv Triv) (,label) (,label))
;	         |	(begin Effect* Tail)
;   Effect  -->	(set! Loc Triv)
;	         |	(set! Loc (binop Triv Triv))
;   Loc     -->	reg | disp-opnd
;   Triv	-->	Loc | int | label
;---------------------------------------------------------------
(define-who expose-basic-blocks
  (define (Tail x)
    (match x
      [(if ,pred ,[conseq cb*] ,[altern ab*])
       (let*-values ([(clab) (unique-label 'c)]
                     [(alab) (unique-label 'a)]
                     [(pred pb*) (Pred pred clab alab)])
         (values pred
           `(,pb* ...
              [,clab (lambda () ,conseq)]
              ,cb* ...
              [,alab (lambda () ,altern)]
              ,ab* ...)))]
      [(begin ,effect* ... ,[tail tb*])
       (let-values ([(x xb*) (Effect* effect* `(,tail))])
         (values x `(,xb* ... ,tb* ...)))]
      [(,triv) (values `(,triv) '())]
      [,x (error who "malformed Tail ~s" x)]))
  (define (Pred x tlab flab)
    (match x
      [(true) (values `(,tlab) '())]
      [(false) (values `(,flab) '())]
      [(begin ,ef* ... ,pred)
       (let*-values ([(pred pb*) (Pred pred tlab flab)]
                     [(x xb*) (Effect* ef* `(,pred))])
         (values x
           `(,xb* ... ,pb* ...)))]
      [(if ,pred ,cpred ,apred)
       (let*-values ([(cplab) (unique-label 'c)]
                     [(aplab) (unique-label 'a)]
                     [(cpred cpb*) (Pred cpred tlab flab)]
                     [(apred apb*) (Pred apred tlab flab)]
                     [(pred pb*) (Pred pred cplab aplab)])
         (values pred
           `(,pb* ...
              [,cplab (lambda () ,cpred)]
              ,cpb* ...
              [,aplab (lambda () ,apred)]
              ,apb* ...)))]
      [(,relop ,triv1, triv2)
       (values
         `(if (,relop ,triv1 ,triv2) (,tlab) (,flab))
                                '())]
      [,x (error who "malformed Pred ~s" x)]))
  (define (Effect* x* tail*)
    (match x*
      [() (values (make-begin tail*) '())]
      [(,x* ... (set! ,a (,binop ,a ,b)))
       (Effect* x* `((set! ,a (,binop ,a ,b)) ,tail* ...))]
      [(,x* ... (set! ,var ,rhs))
       (Effect* x* `((set! ,var ,rhs) ,tail* ...))]
      [(,x* ... (if ,pred ,ef1 ,ef2))
       (let*-values ([(jlab) (unique-label 'j)]
                     [(clab) (unique-label 'c)]
                     [(alab) (unique-label 'a)]
                     [(conseq cb*) (Effect* `(,ef1) `((,jlab)))]
                     [(altern ab*) (Effect* `(,ef2) `((,jlab)))]
                     [(pred pb*) (Pred pred clab alab)]
                     [(x xb*) (Effect* x* `(,pred))])
         (values x
           `(,xb* ... ,pb* ...
              [,clab (lambda () ,conseq)]
              ,cb* ...
              [,alab (lambda () ,altern)]
              ,ab* ...
              [,jlab ,`(lambda () ,(make-begin tail*))])))]

      ; no need to handle ending effect separately or 
      ; even effects before and after begin separately
      ; since we have verified the source already. So
      ; we know all these x* and ef* are just effects.
      ; In fact, handling them separately may result in
      ; nested begins, which is not in accordance with
      ; output grammar.
      [(,x* ... (begin ,ef* ...))
       (Effect* `(,x* ... ,ef* ...) tail*)]
      [(,x* ... (nop))
       (Effect* x* tail*)]
      [,x (error who "malformed Effect ~s" x)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Tail -> tail* b**])] ...) ,[Tail -> tail b*])
       `(letrec ([,label* (lambda () ,tail*)] ... ,b** ... ... ,b* ...) ,tail)]
      [,x (error who "malformed Program ~s" x)])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   flatten-program
;
; Description: 
;   Accepts the input from expose-basic-blocks and flattens
;   the program. The entire program is wrapped inside a
;   list with car equals to 'code. The Tail (body) of the
;   letrec appears next in the list. Then each of the labels,
;   followed by the body (without 'begin) of the thunk, 
;   follows. The calls of the form (Triv) are changed to 
;   (jump Triv). The "if" forms are changed into conditional
;   jumps of the form cmpq following either jl, jle, je, jne,
;   jg, jge. An optimization is done to avoid unnecessary 
;   jumps when the target of a jump is equal to the next label.
;   
; Input Language:  
;   Same as the output language of expose-basic-blocks
;
; Output Language: 
;   (code Tail Label1 Tail1 Label2 Tail2 ...)
;   Each Tail of the original thunks are preceeded by
;   its label. See Description.
;---------------------------------------------------------------
(define-who flatten-program
  (define (Tail tail nextlab)
    (match tail
      [(begin ,ef* ... ,[tail]) `(,ef* ... ,tail ...)]
      [(,t) (if (not (eqv? nextlab t)) `((jump ,t)) '())]
      [(if (,relop ,triv1 ,triv2) (,clab) (,alab))
       (case nextlab
         [clab `((if (not (,relop ,triv1 ,triv2)) (jump ,alab)))]
         [alab `((if (,relop ,triv1 ,triv2) (jump ,clab)))]
         [else `((if (,relop ,triv1 ,triv2) (jump ,clab)) (jump ,alab))])]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
       (let ([tail* (map Tail `(,tail ,tail* ...) `(,label* ... ()))])
         `(code ,(car tail*) ...  ,`((,label* ,(cdr tail*) ...) ...) ... ...))])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   generate-x86-64
;
; Description: 
;   Accepts the input from flatten-program and generates
;   equivalent x86_64 assembly instructions. It uses the
;   emit-program, emit-label, emit-jump, and emit in
;   helpers.ss to make things simple and clear.
;   
; Input Language:  
;   Same as the output language of flatten-program
;
; Output Language: 
;   subset of x86_64 assembly language
;---------------------------------------------------------------
(define-who generate-x86-64
  (define ops '((+ . addq) (- . subq) (* . imulq) (logand . andq) 
                   (logor . orq) (sra . sarq) (= . je) (< . jl) (<= . jle)
                   (> . jg) (>= . jge)))
  (define invops '((= . jne) (< . jge) (<= . jg) (> . jle) (>= . jl)))
  (define Code
    (lambda (s)
      (match s
        [(set! ,x (,binop ,x ,triv)) (emit (cdr (assq binop ops)) triv x)]
        ; if triv is a label we want to set the effective address to
        ; var rather the instruction/value referred by the address of
        ; label.
        [(set! ,var ,triv) (if (label? triv) 
                               (emit 'leaq triv var)
                               (emit 'movq triv var))]
        [(if (,relop ,triv1 ,triv2) (jump ,lab))
         (emit 'cmpq triv2 triv1)
         (emit-jump (cdr (assq relop ops)) lab)]
        [(if (not (,relop ,triv1 ,triv2)) (jump ,lab))
         (emit 'cmpq triv2 triv1)
         (emit-jump (cdr (assq relop invops)) lab)]
        [(jump ,x) (emit-jump 'jmp x)]
        [,x (guard (label? x)) (emit-label x)])))
  (lambda (s)
    (match s
      [(code ,code* ...) (emit-program (for-each Code code*))])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   everybody-home
;
; Description: 
;   Checks if all the body elements have gone
;   through the register/frame allocator completely
;
; Input Language:  
;   Same as the out of assign-registers
;
; Output Language: 
;   #t or #f
;---------------------------------------------------------------
(define-who everybody-home?
  (define all-home?
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (spills (,spill* ...)
               (locate (,home* ...)
                 (frame-conflict ,ct ,tail))))) #f]
        [(locate (,home* ...) ,tail) #t]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
       [(letrec ([,label* (lambda () ,body*)] ...) ,body)
        (andmap all-home? `(,body ,body* ...))]
       [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Helpers
;---------------------------------------------------------------
;; returns a sub set of items which satisfies the 
;; predicate from the given set, l
(define select
  (lambda (predicate? l)
    (match l
      [() '()]
      [(,item . ,[l]) (if (predicate? item) `(,item . ,l) l)])))

(define select-uvar-or
  (lambda (what? l)
    (select (lambda (item) (or (uvar? item) (what? item))) l))) 
(define select-indirect
  (lambda (uvar* home*)
    (remq #f (map (lambda (uvar)
                    (let ([p (assq uvar home*)])
                      (if p
                          (cadr p)
                          #f))) uvar*))))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Helper for both uncover-register-conflict and 
; uncover-frame-conflict passes          
;
; Description: 
;   Uncovers conflicts based on the given what? predicate
;---------------------------------------------------------------
(define-who uncover-conflict
  (lambda (what?)
    (define handle-assignment!
      (lambda (var liveset alist)
        (cond
         [(what? var)
          (set-conflicts! (select uvar? liveset) alist var)]
         [(uvar? var)
          (let ([row (assq var alist)])
            (set-cdr! row (union liveset (cdr row)))
            (set-conflicts! (select uvar? liveset) alist var))])))
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
          [(,triv ,loc* ...) (union liveset 
                                    (select-uvar-or what? `(,triv)) 
                                    (select-uvar-or what? loc*))]
          [,x (error who "invalid Tail ~s" x)])))
    (define Pred
      (lambda (pred alist trueset falseset)
        (match pred
          [(true) trueset]
          [(false) falseset]
          [(begin ,ef* ... ,[predset]) (Effect* ef* alist predset)]
          [(if ,pred ,[trueset] ,[falseset]) (Pred pred alist trueset falseset)]
          [(,relop ,triv1 ,triv2)
           (union trueset falseset (select-uvar-or what? `(,triv1 ,triv2)))]
          [,x (error who "invalid Pred ~s" x)])))
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
          [(,x* ... (set! ,var (,binop ,triv1 ,triv2)))
           (let ([liveset (remq var liveset)])
             (handle-assignment! var liveset alist)
             (Effect* x* alist (union liveset (select-uvar-or what? `(,triv1 ,triv2)))))]
          [(,x* ... (set! ,var ,triv))
           (let ([liveset (remq var liveset)])
             (handle-assignment! var (remq triv liveset) alist)
             (Effect* x* alist (union liveset (select-uvar-or what? `(,triv)))))]
          [,x (error who "invalid Effect* ~s" x)])))
    Tail))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   uncover-frame-conflict
;
; Description: 
;   Unocovers frame conflicts.
;
; Input Language:  
;   Same as the output of verify-scheme
;
; Output Language: 
;   Only change is 
;   Body --> (locals (uvar*)
;		       (frame-conflict conflict-graph Tail)
;---------------------------------------------------------------
(define-who uncover-frame-conflict
  (define Body
    (lambda (body)
      (match body
        [(locals (,uvar* ...) ,tail)
         (let([fcg* `((,uvar*) ...)])
           ((uncover-conflict frame-var?) tail fcg* '()) ; neglect the returned liveset
           `(locals (,uvar* ...) (frame-conflict ,fcg* ,tail)))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   introduce-allocation-forms
;
; Description: 
;   The superficial pass to add allocation forms
;---------------------------------------------------------------
(define-who introduce-allocation-forms
  (define Body
    (lambda (body)
      (match body
        [(locals (,uvar* ...) (frame-conflict ,fcg* ,tail))
         `(locals (,uvar* ...) 
            (ulocals ()
              (locate ()
                (frame-conflict ,fcg* ,tail))))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   select-instructions
;
; Description: 
;   Corrects any invalid, w.r.t. x84_64 architecture, effect.
;   Possibly introduce unspillables.
;
; Input:
;   Same as the output of introduce-allocation-forms
;
; Output:
;   Same as input except the possible introduction of unspillables
;   and modified effects.
;
;   Body --> (locals (uvar*)
;	          (ulocals (uvar*)
;		       (locate ([uvar fvar]*)
;		        (frame-conflict conflict-graph Tail))))
;	       | (locate ([uvar Loc]*) Tail)
;---------------------------------------------------------------
(define-who select-instructions
  (define com* '(+ * logand logor)) ;; specifies the commutative operators
  (define reverse* '((< . >) (<= . >=) (> . <) (>= . <=) (= . =))) ;; specifies reverse of relops
  ;; returns true iff triv is either register or uvar
  (define uvar-or-reg?
    (lambda (triv)
      (or (register? triv) (uvar? triv))))
  (define var?
    (lambda (triv)
      (or (uvar-or-reg? triv) (frame-var? triv))))
  (define strictly-int64?
    (lambda (x)
      (and (not (int32? x)) (int64? x))))
  (define Body
    (lambda (body)
      (define newulocal* '())
      (define newu
        (lambda ()
          (set! newulocal* (cons (unique-name 't) newulocal*))
          (car newulocal*)))
      (define Pred
        (lambda (pred)
          (match pred
            [(true) '(true)]
            [(false) '(false)]
            [(if ,[pred] ,[conseq] ,[alter])
             `(if ,pred ,conseq ,alter)]
            [(begin ,[Effect -> ef*] ... ,[pred])
             (make-begin `(,ef* ... ,pred))]
            [(,relop ,x ,y) (Relop `(,relop ,x ,y))]
            [,x (error who "invalid Pred ~s" x)])))
      (define Effect
        (lambda (ef)
          (match ef
            [(nop) '(nop)]
            [(set! ,x (,binop ,y ,z)) (Binop `(set! ,x (,binop ,y ,z)))]
            [(set! ,x ,y) (Move `(set! ,x ,y))]
            [(if ,[Pred -> pred] ,[conseq] ,[alter]) 
             `(if ,pred ,conseq ,alter)]
            [(begin ,[ef*] ...) (make-begin ef*)])))
      (define Tail
        (lambda (tail)
          (match tail
            [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
             (make-begin `(,ef* ... ,tail))]
            [(if ,[Pred -> pred] ,[conseq] ,[alter])
             `(if ,pred ,conseq ,alter)]
            [(,triv ,loc* ...) `(,triv ,loc* ...)]
            [,x (error who "invalid Tail ~s" x)])))
      (define Move
        (lambda (ef)
          (match ef
            [(set! ,x ,y)
             (if (and (frame-var? x) (or (frame-var? y) (strictly-int64? y) (label? y)))
                 (let ([u (newu)]) 
                   (make-begin
                    `((set! ,u ,y)
                      (set! ,x ,u))))
                 `(set! ,x ,y))])))
      (define Binop
        (lambda (ef)
          (match ef
            [(set! ,x (,op ,y ,z))
             (cond
              [(eq? x y) (Binop2 `(set! ,x (,op ,x ,z)))]
              [(and (eq? x z) (memq op com*)) (Binop2 `(set! ,x (,op ,x ,y)))]
              [else (let ([u (newu)])
                      (make-begin 
                       `((set! ,u ,y)
                         ,(Binop2 `(set! ,u (,op ,u ,z)))
                         (set! ,x ,u))))])])))
      (define Binop2
        (lambda (ef)
          (match ef
            [(set! ,var (,op ,var ,triv))
             (cond
              [(and (eq? '* op)
                    (frame-var? var))
               (let ([u (newu)])
                 (make-begin
                  `((set! ,u ,var)
                    ,(Binop2 `(set! ,u (* ,u ,triv)))
                    (set! ,var ,u))))]
              ;; Note: if op is sra, verify-scheme guarantees that 
              ;;       it will fall into this condition with triv 
              ;;       as int32. So we need not to handle sra separately.
              [(or (and (uvar-or-reg? var)
                        (or (var? triv) (int32? triv)))
                   (and (frame-var? var)
                        (or (uvar-or-reg? triv) (int32? triv))))
               `(set! ,var (,op ,var ,triv))]
              [(or (and (frame-var? var)
                        (or (frame-var? triv) (strictly-int64? triv) (label? triv)))
                   (and (uvar-or-reg? var)
                        (or (strictly-int64? triv) (label? triv))))
               (let ([u (newu)])
                 (make-begin
                  `((set! ,u ,triv)
                    (set! ,var (,op ,var ,u)))))])])))
      (define Relop
        (lambda (pred) 
          (match pred
            [(,op ,triv1 ,triv2) 
             (cond
              [(var? triv1) (Relop2 `(,op ,triv1 ,triv2))]
              [(var? triv2) (Relop2 `(,(cdr (assq op reverse*)) ,triv2 ,triv1))]
              [else (let ([u (newu)])
                      (make-begin 
                       `((set! ,u ,triv1)
                         ,(Relop2 `(,op ,u ,triv2)))))])])))
      (define Relop2
        (lambda (pred)
          (match pred
            [(,op ,var ,triv)
             (cond
              [(or (and (uvar-or-reg? var)
                        (or (var? triv) (int32? triv)))
                   (and (frame-var? var)
                        (or (uvar-or-reg? triv) (int32? triv))))
               `(,op ,var ,triv)]
              [(or (and (uvar-or-reg? var)
                        (or (strictly-int64? triv) (label? triv)))
                   (and (frame-var? var)
                        (or (frame-var? triv) (strictly-int64? triv) (label? triv))))
               (let ([u (newu)])
                 (make-begin
                  `((set! ,u ,triv)
                    (,op ,var ,u))))])])))
      
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (locate ([,uvar* ,fvar*] ...)
               (frame-conflict ,fcg* ,[Tail -> tail]))))
         `(locals (,local* ...)
            (ulocals (,ulocal* ... ,newulocal* ...)
              (locate ([,uvar* ,fvar*] ...)
                (frame-conflict ,fcg* ,tail))))] ; do nothing at the moment
        [(locate ([,uvar* ,loc*] ...) ,tail)
         `(locate ([,uvar* ,loc*] ...) ,tail)] ; output same for complete body
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   uncover-register-conflict
;
; Description: 
;   Unocovers register conflicts.
;
; Input Language:  
;   Same as the output of select-instructions
;
; Output Language: 
;   The only change is,
;   Body --> (locals (uvar*)
;	          (ulocals (uvar*)
;		       (locate ([uvar fvar]*)
;		        (frame-conflict conflict-graph
;		         (register-conflict conflict-graph Tail)))))
;    	   | (locate ([uvar Loc]*) Tail)
;---------------------------------------------------------------
(define-who uncover-register-conflict
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...) 
           (ulocals (,ulocal* ...)
             (locate ([,uvar* ,fvar*] ...)
               (frame-conflict ,fcg* ,tail))))
         (let ([rcg* `((,local*) ... (,ulocal*) ...)])
           ((uncover-conflict register?) tail rcg* '()) ; neglect the returned live list
           `(locals (,local* ...)
              (ulocals (,ulocal* ...)
                (locate ([,uvar* ,fvar*] ...)
                  (frame-conflict ,fcg* 
                    (register-conflict ,rcg* ,tail))))))]
        [(locate ([,uvar* ,loc*] ...) ,tail)
         `(locate ([,uvar* ,loc*] ...) ,tail)] ; output same for complete body
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
;   Tries to assign registers for all the spillables and 
;   unspillables
;
; Input Language:  
;   Same as the output of uncover-register-conflict
;
; Output Language: 
;   The only change is,
;   Body --> (locals (uvar*)
;		      (ulocals (uvar*)
;		       (spills (uvar*)
;		        (locate ([uvar fvar]*)
;		         (frame-conflict conflict-graph Tail)))))
;	     |	(locate ([uvar Loc]*) Tail)
;---------------------------------------------------------------
(define-who assign-registers
  (define k (length registers))
  (define pick-if
    (lambda (pred? cg)
      (cond
       [(null? cg) #f]
       [(pred? (car cg)) (car cg)]
       [else (pick-if pred? (cdr cg))])))
  (define low-degree?
    (lambda (row)
      (< (sub1 (length row)) k)))
  (define pick-one
    (lambda (cg ulocal*)
      (let* ([spillable? (lambda (row)
                           (not (memq (car row) ulocal*)))]
             [pick (or (pick-if low-degree? cg) (pick-if spillable? cg))])
        (if pick pick (error  who "Only high-degree unspillables are left")))))
  (define remove-conflicts!
    (lambda (pick cg)
      (for-each (lambda (row)
                  (set-cdr! row (remq (car pick) (cdr row)))) cg)))
  (define simplify-and-select
    (lambda (uvar* ulocal* cg) ;; uvar* contains locals and ulocal* (unspillables)
      (if (null? uvar*)
          (values '() '()) ; if uvar* is null no assignments & spills
          (let* ([pick (pick-one cg ulocal*)] [cg (remq pick cg)])
            (remove-conflicts! pick cg)
            (let*-values
                ([(alist spills) (simplify-and-select (remq (car pick) uvar*) ulocal* cg)]
                 [(pickregs) (select register? (cdr pick))] ; registers in picked row
                 [(otherregs)  (select-indirect (difference (cdr pick) pickregs) alist)]
                 [(availregs) (difference registers (union pickregs otherregs))])
              (if (not (null? availregs))
                  (values
                    (cons `(,(car pick) ,(car availregs)) alist)
                    spills)
                  (values alist (cons (car pick) spills))))))))
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (locate ([,uvar* ,fvar*] ...)
               (frame-conflict ,fcg*
                 (register-conflict ,rcg* ,tail)))))
         (let-values ([(homes* spill*) 
                       (simplify-and-select `(,local* ... ,ulocal* ...) ulocal* rcg*)])
           (if (null? spill*)
               `(locate ([,uvar* ,fvar*] ... ,homes* ...) ,tail)
               `(locals ,(difference local* spill*)
                  (ulocals (,ulocal* ...)
                    (spills ,spill*
                      (locate ([,uvar* ,fvar*] ...) ;; discard assigned homes*
                        (frame-conflict ,fcg* ,tail)))))))] ;; drop register-conflict form
        [(locate ([,uvar* ,loc*] ...) ,tail)
         `(locate ([,uvar* ,loc*] ...) ,tail)] ;; output same for complete body
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   assign-frame
;
; Description: 
;   Assign frames for spilled variables
;
; Input Language:  
;   Same as the output of assign-registers
;
; Output Language: 
;   The only change is,
;   Body --> (locals (uvar*)
;		      (ulocals (uvar*)
;		       (locate ([uvar fvar]*)
;		        (frame-conflict conflict-graph Tail))))
;	      |  (locate ([uvar Loc]*) Tail)
;---------------------------------------------------------------
(define-who assign-frame
  (define pick-avail
    (lambda (unavail* base)
      (let ([pick (index->frame-var base)])
        (if (not (memq pick unavail*))
            pick
            (pick-avail unavail* (add1 base))))))
  (define select-frames
    (lambda (spill* fcg* home*)
      (map (lambda (spill)
             (let* ([row (assq spill fcg*)]
                    [direct* (select frame-var? (cdr row))]
                    [indirect* (select-indirect (difference (cdr row) direct*) home*)]
                    [pick (pick-avail (union direct* indirect*) 0)])
               (set! home* (cons `(,spill ,pick) home*))
               `(,spill ,pick))) spill*)))
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (spills (,spill* ...)
               (locate ([,uvar* ,fvar*] ...)
                 (frame-conflict ,fcg* ,tail)))))
         (let ([home* (select-frames spill* fcg* `([,uvar* ,fvar*] ...))])
           `(locals (,local* ...)
              (ulocals (,ulocal* ...)
                (locate ([,uvar* ,fvar*] ... ,home* ...)
                  (frame-conflict ,fcg* ,tail)))))]
        [(locate ([,uvar* ,loc*] ...) ,tail)
         `(locate ([,uvar* ,loc*] ...) ,tail)] ;; output same for complete body
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   finalize-frame-locations
;
; Description: 
;   Replaces each occurence of frame assigned variables with
;   the corresponding frame.
;---------------------------------------------------------------
(define-who finalize-frame-locations
  ;; if v is uvar then try to find the assigned fvar 
  ;; if any from env. If found then return it else
  ;; return v as it is. Also if v is not uvar then 
  ;; return it as it is
  (define uvar->fvar
    (lambda (v env)
      (if (uvar? v) 
          (let ([home (assq v env)])
            (if home
                (cdr home)
                v))
          v)))
  (define Pred
    (lambda (env)
      (lambda (pred)
        (match pred
          [(true) '(true)]
          [(false) '(false)]
          [(if ,[(Pred env) -> pred] ,[(Pred env) -> pred1] ,[(Pred env) -> pred2])
           `(if ,pred ,pred1 ,pred2)]
          [(begin ,[(Effect env) -> ef*] ... ,[(Pred env) -> pred])
           `(begin ,ef* ... ,pred)]
          [(,relop ,x ,y)
           `(,relop ,(uvar->fvar x env) ,(uvar->fvar y env))]
          [,x (error who "invalid Pred ~s" x)]))))
  (define Effect
    (lambda (env)
      (lambda (ef)
        (match ef
          [(set! ,x (,binop ,x ,y))
           ;; uvar->fvar will resolve a uvar, x, to it's frame location. 
           ;; If x is not a uvar or not assigned frame then it's returned
           ;; as it is.
           (let ([x (uvar->fvar x env)] [y (uvar->fvar y env)])
             `(set! ,x (,binop ,x ,y)))]
          [(set! ,x ,y)
           (let ([x (uvar->fvar x env)] [y (uvar->fvar y env)])
             (if (eq? x y) '(nop) `(set! ,x ,y)))]
          [(if ,[(Pred env) -> pred] ,[(Effect env) -> ef1] , [(Effect env) -> ef2])
           `(if ,pred ,ef1 ,ef2)]
          [(begin ,[(Effect env) -> ef*] ... ,[(Effect env) -> ef])
           `(begin ,ef* ... ,ef)]
          [(nop) '(nop)]))))
  (define Tail
    (lambda (env)
      (lambda (tail)
        (match tail
          [(begin ,[(Effect env) -> ef*] ... ,[(Tail env) -> tail])
           `(begin ,ef* ... ,tail)]
          [(if ,[(Pred env) -> pred] ,[(Tail env) -> tail1] ,[(Tail env) -> tail2])
           `(if ,pred ,tail1 ,tail2)]
          [(,triv ,loc* ...)
           `(,(uvar->fvar triv env) ,loc* ...)]
          [,x (error who "invalid Tail ~s" x)]))))
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (locate ([,uvar* ,fvar*] ...)
               (frame-conflict ,fcg* ,tail))))
         `(locals (,local* ...)
            (ulocals (,ulocal* ...)
              (locate ([,uvar* ,fvar*] ...)
                (frame-conflict ,fcg* ,((Tail (map cons uvar* fvar*)) tail)))))]
        [(locate ([,uvar* ,loc*] ...) ,tail)
         `(locate ([,uvar* ,loc*] ...) ,tail)] ;; output same for complete body
        [,x (error who "invalid Body ~s" x)])))
  (lambda (s)
    (match s
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   finalize-locations
;
; Description: 
;   Relies on the output of discard-call-live pass and
;   replaces location aliases with the actual register
;   variable. It also discards the locate form presented
;   in the input grammer. 
;
; Input Language:  
;   Same as the input language to verify-scheme
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Tail)]*) Tail)
;   Tail	-->	(Triv)
;	         |	(if Pred Tail Tail)
;	         |	(begin Effect* Tail)
;   Pred	-->	(true)
;	         |	(false)
;	         |	(relop Triv Triv)
;            |	(if Pred Pred Pred)
;	         |	(begin Effect* Pred)
;   Effect	-->	(nop)
;	         |	(set! Loc Triv)
;	         |	(set! Loc (binop Triv Triv))
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Triv	-->	Loc | int | label
;---------------------------------------------------------------
(define-who finalize-locations
  (define uvar->reg
    (lambda (v env)
      (if (uvar? v) (cdr (assq v env)) v)))
  (define Pred
    (lambda (env)
      (lambda (pred)
        (match pred
          [(true) '(true)]
          [(false) '(false)]
          [(if ,[(Pred env) -> pred] ,[(Pred env) -> pred1] ,[(Pred env) -> pred2])
           `(if ,pred ,pred1 ,pred2)]
          [(begin ,[(Effect env) -> ef*] ... ,[(Pred env) -> pred])
           `(begin ,ef* ... ,pred)]
          [(,relop ,x ,y)
           `(,relop ,(uvar->reg x env) ,(uvar->reg y env))]
          [,x (error who "invalid Pred ~s" x)]))))
  (define Effect
    (lambda (env)
      (lambda (ef)
        (match ef
          [(set! ,x (,binop ,x ,y))
           ;; uvar->reg will resolve a uvar, x, to it's register
           ;; location. If x is not a uvar then it's returned as 
           ;; it is. This is guaranteed to replace only register
           ;; associations as frame associations have already
           ;; taken care by previous finalize-frame-locations pass.
           (let ([x (uvar->reg x env)] [y (uvar->reg y env)])
             `(set! ,x (,binop ,x ,y)))]
          [(set! ,x ,y)
           (let ([x (uvar->reg x env)] [y (uvar->reg y env)])
             (if (eq? x y) '(nop) `(set! ,x ,y)))]
          [(if ,[(Pred env) -> pred] ,[(Effect env) -> ef1] , [(Effect env) -> ef2])
           `(if ,pred ,ef1 ,ef2)]
          [(begin ,[(Effect env) -> ef*] ... ,[(Effect env) -> ef])
           `(begin ,ef* ... ,ef)]
          [(nop) '(nop)]))))
  (define Tail
    (lambda (env)
      (lambda (tail)
        (match tail
          [(begin ,[(Effect env) -> ef*] ... ,[(Tail env) -> tail])
           `(begin ,ef* ... ,tail)]
          [(if ,[(Pred env) -> pred] ,[(Tail env) -> tail1] ,[(Tail env) -> tail2])
           `(if ,pred ,tail1 ,tail2)]
          [(,triv)
           `(,(uvar->reg triv env))]
          [,x (error who "invalid Tail ~s" x)]))))
  (define Body
    (lambda (body)
      (match body
        [(locate ([,uvar* ,loc*] ...) ,tail)
         ((Tail (map cons uvar* loc*)) tail)]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (s)
    (match s
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------
