; Saliya Ekanayake
; sekanaya
; Assignment 7

;---------------------------------------------------------------
; Helpers
;---------------------------------------------------------------
(define op?
  (lambda (op)
    (or (binop? op) (memq op '(< <= > >= =)))))
(define binop?
  (lambda (binop)
    (memq binop '(+ - * logand logor sra))))

(define triv?
  (lambda (t)
    (or (label? t) (uvar? t) (and (integer? t) (exact? t)))))

(define uvar-or-frame-var?
  (lambda (var)
    (or (uvar? var) (frame-var? var))))

(define uvar-or-register?
  (lambda (var)
    (or (uvar? var) (register? var))))

(define select-indirect
  (lambda (uvar* home*)
    (let f ([uvar* uvar*][indirect* '()])
      (cond
       [(null? uvar*) indirect*]
       [else (let ([p (assq (car uvar*) home*)])
               (f (cdr uvar*) (if p (cons (cadr p) indirect*) indirect*)))]))))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   remove-complex-opera*
;
; Description: 
;   This pass removes arbitary nesting of operators
;   operands. It uses set! to assign any complex Value
;   to a fresh variable before the call.
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
;   Tail	-->	Triv
;	         |	(binop Value Value)
;	         |	(Value Value*)
;	         |	(if Pred Tail Tail)
;	         |	(begin Effect* Tail)
;   Pred	-->	(true)
;	         |	(false)
;	         |	(relop Value Value)
;            |	(if Pred Pred Pred)
;	         |	(begin Effect* Pred)
;  Effect	-->	(nop)
;	         |	(set! uvar Value)
;            |  (Value Value*)
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;  Value	-->	Triv
;	         |	(binop Value Value)
;	         |	(if Pred Value Value)
;            |  (Value Value*)
;	         |	(begin Effect* Value)
;   Triv	-->	uvar | int | label 
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
;   Tail	-->	Triv
;			 |	(binop Triv Triv)
;			 |	(Triv Triv*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;  Effect	-->	(nop)
;			 |	(set! uvar Value)
;            |  (Triv Triv*)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;  Value	-->	Triv
;			 |	(binop Triv Triv)
;			 |	(if Pred Value Value)
;			 |	(begin Effect* Value)
;            |  (Triv Triv*)
;   Triv	-->	uvar | int | label
;---------------------------------------------------------------
(define-who remove-complex-opera*
  (define (Body bd)
    (define new-local* '())
    (define (new-t)
      (let ([t (unique-name 't)])
        (set! new-local* (cons t new-local*))
        t))
    (define (trivialize-call expr*)
      (let-values ([(call set*) (break-down-expr* expr*)])
        (make-begin `(,@set* ,call))))
    (define (break-down-expr* expr*)
      (match expr*
        [() (values '() '())]
        [(,s . ,[rest* set*])
         (guard (simple? s))
         (printf "\n***************\n~s\n***************\n" s)
         (values `(,s ,rest* ...) set*)]
        [(,[Value -> expr] . ,[rest* set*])
         (let ([t (new-t)])
           (values `(,t ,rest* ...) `((set! ,t ,expr) ,set* ...)))]
        [,expr* (error who "invalid Expr ~s" expr*)]))
    (define (simple? x)
      (or (uvar? x) (label? x) (and (integer? x) (exact? x))
          (memq x '(+ - * logand logor sra)) (memq x '(= < <= > >=))))
    (define (triv? x) (or (uvar? x) (int64? x) (label? x)))
    (define (Value val)
      (match val
        [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[val]) (make-begin `(,ef* ... ,val))]
        [(,binop ,x ,y)
         (guard (memq binop '(+ - * logand logor sra)))
         (trivialize-call `(,binop ,x ,y))]
        [(,rator ,rand* ...) (trivialize-call `(,rator ,rand* ...))]
        [,tr (guard (triv? tr)) tr]
        [,val (error who "invalid Value ~s" val)]))
    (define (Effect ef)
      (match ef
        [(nop) '(nop)]
        [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
        [(set! ,var ,[Value -> val]) `(set! ,var ,val)]
        [(,rator ,rand* ...) (trivialize-call `(,rator ,rand* ...))]
        [,ef (error who "invalid Effect ~s" ef)]))
    (define (Pred pr)
      (match pr
        [(true) '(true)]
        [(false) '(false)]
        [(if ,[test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[pr]) (make-begin `(,ef* ... ,pr))]
        [(,relop ,x ,y)
         (guard (memq relop '(< <= = >= >)))
         (trivialize-call `(,relop ,x ,y))]
        [,pr (error who "invalid Pred ~s" pr)]))
    (define (Tail tail)
      (printf "\n***************\n~s\n***************\n" tail)
      (match tail
        [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[tail]) (make-begin `(,ef* ... ,tail))]
        [(,binop ,x ,y)
         (guard (memq binop '(+ - * logand logor sra)))
         (trivialize-call `(,binop ,x ,y))]
        [(,rator ,rand* ...) (trivialize-call `(,rator ,rand* ...))]
        [,tr (guard (triv? tr)) tr]
        [,tail (error who "invalid Tail ~s" tail)]))
    (match bd
      [(locals (,local* ...) ,[Tail -> tail])
       `(locals (,local* ... ,new-local* ...) ,tail)]
      [,bd (error who "invalid Body ~s" bd)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,[Body -> bd*])] ...)
         ,[Body -> bd])
       `(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   flatten-set!
;
; Description: 
;   Rewrites set! operations so that they will not contain
;   begin or if expressions on their right hand sides. It
;   does so by pushing set! into begin and if expressions.
;
; Input Language:  
;   Same as the output of remove-complex-opera* pass.
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
;   Tail	-->	Triv
;			 |	(binop Triv Triv)
;			 |	(Triv Triv*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;  Effect	-->	(nop)
;			 |	(set! uvar Triv)
;            |  (set! uvar (binop Triv Triv))
;            |  (set! uvar (Triv Triv*))
;            |  (Triv Triv*)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Triv	-->	uvar | int | label
;---------------------------------------------------------------
(define-who flatten-set!
  (define handle-set!
    (lambda (uvar val)
      (match val
        [(if ,[Pred -> pred] ,conseq ,alter)
         `(if ,pred ,(handle-set! uvar conseq) ,(handle-set! uvar alter))]
        [(begin ,[Effect -> ef*] ... ,val)
         (make-begin `(,ef* ... ,(handle-set! uvar val)))]
        [(,binop ,triv1 ,triv2) (guard (binop? binop))
         `(set! ,uvar (,binop ,triv1 ,triv2))]
        [(,triv ,triv* ...) `(set! ,uvar (,triv ,triv* ...))]
        [,triv (guard (triv? triv)) `(set! ,uvar ,triv)]
        [,x (error who "invalid Value ~s" x)])))
  (define Effect
    (lambda (ef)
      (match ef
        [(nop) `(nop)]
        [(begin ,[ef*] ...) (make-begin ef*)]
        [(if ,[Pred -> pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(set! ,uvar ,val) (handle-set! uvar val)]
        [(,triv ,triv* ...) `(,triv ,triv* ...)]
        [,x (error who "invalid Effect ~s" x)])))
  (define Pred
    (lambda (pred)
      (match pred
        [(true) '(true)]
        [(false) '(false)]
        [(begin ,[Effect -> ef*] ... ,[pred])
         (make-begin `(,ef* ... ,pred))]
        [(if ,[pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(,relop ,triv1 ,triv2) `(,relop ,triv1 ,triv2)])))
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[tail])
         (make-begin `(,ef* ... ,tail))]
        [(if ,[Pred -> pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(,binop ,triv1 ,triv2) (guard (binop? binop))
         `(,binop ,triv1 ,triv2)]
        [(,triv ,triv* ...) `(,triv ,triv* ...)]
        [,triv (guard (triv? triv)) triv]
        [,x (error who "invalid Tail ~s" x)])))
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...) ,[Tail -> tail])
         `(locals ,local* ,tail)]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,param** ...) ,body*)] ...) ,body)
       `(letrec ([,label* (lambda (,param** ...) ,(map Body body*))] ...)
          ,(Body body))]
      [,x (error who "invalid Body ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   impose-calling-conventions
;
; Description: 
;   This pass imposes the simple set of calling conventions 
;   used in our grammar. It first converts lambda bodies 
;   into a form where all the formal parameters are placed
;   as locals. It also add a fresh variable, rp, to denote
;   the return address register. Then it assigns the parameters
;   with the respective register/frame values based on the 
;   convention. Then for each function call it will store 
;   back the values of the argument variables into respective
;   register/frame locations (again based on the convention).
;   It will also store the value of rp into return address 
;   register. These locations along with the frame pointer
;   register are then placed as live in the call. In the case 
;   of primitive calls return value register (rv) is stored with 
;   the particular expression. Then a call is added to rp with 
;   fp and rv as live locations.
;
;   In the case of non tail calls this will introduce the
;   new-frames form with a set of set of new unique variables
;   indicating the required set of frame variables for each 
;   non tail call in the body. These new uvars are also added
;   to the locals form for the sake of remaining passes.
;
; Input Language:  
;   Same as the output of flatten-set! pass.
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) (new-frames (frame*) Tail))
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! uvar Triv)
;            |  (set! uvar (binop Triv Triv))
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;---------------------------------------------------------------
(define-who impose-calling-conventions
  (define preglen (lambda () (length parameter-registers)))
  (define param-locations
    (lambda (param*)
      (let gen ([param* param*] [preg parameter-registers] [fv-index 0])
        (cond
         [(null? param*) '()]
         [(null? preg) (cons (index->frame-var fv-index)
                             (gen (cdr param*) preg (add1 fv-index)))]
         [else (cons (car preg) (gen (cdr param*) (cdr preg) fv-index))]))))
  (define Body
    (lambda (body param*)
      (define newframe** '())
      (define (gen-newframe*)
        (set! newframe** (cons '() newframe**))
        (lambda ()
          (let ([newf (unique-name 'nfv)])
            (set-car! newframe** (cons newf (car newframe**)))
            newf)))
      (define (nt-arg-locations arg* gen-newframe)
        (let gen ([arg* arg*] [preg parameter-registers])
          (cond
           [(null? arg*) '()]
           [(null? preg) (cons (gen-newframe) (gen (cdr arg*) preg))]
           [else (cons (car preg) (gen (cdr arg*) (cdr preg)))])))
      (define (Triv t) (if (triv? t) t (error who "invalid Triv ~s" t)))
      (define (Pred pred)
        (match pred
          [(true) '(true)]
          [(false) '(false)]
          [(if ,[pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
          [(begin ,[Effect -> ef*] ... ,[pred]) (make-begin `(,ef* ... ,pred))]
          [(,relop ,[Triv -> x] ,[Triv -> y]) `(,relop ,x ,y)]
          [,x (error who "invalid Pred ~s" x)]))
      (define (Effect ef)
        (match ef
          [(nop) '(nop)]
          [(if ,[Pred -> pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
          [(begin ,[Effect -> ef*] ... ,[Effect -> ef]) (make-begin `(,ef* ... ,ef))]
          [(set! ,uvar (,binop ,[Triv -> x] ,[Triv -> y])) (guard (binop? binop))
           `(set! ,uvar (,binop ,x ,y))]
          [(set! ,uvar (,[Triv -> rator] ,[Triv -> rand*] ...))
           (make-begin
            `(,(Effect `(,rator ,rand* ...))
               (set! ,uvar ,return-value-register)))]
          [(set! ,uvar ,[Triv -> triv]) `(set! ,uvar ,triv)]
          [(,[Triv -> rator] ,[Triv -> rand*] ...)
           (let ([nt-arg-loc* (nt-arg-locations rand* (gen-newframe*))]
                 [rp-label (unique-label 'rp)])
             `(return-point ,rp-label
                            ,(make-begin
                              `((set! ,(reverse nt-arg-loc*) ,(reverse rand*)) ...
                                (set! ,return-address-register ,rp-label)
                                (,rator ,frame-pointer-register ,return-address-register ,nt-arg-loc* ...)))))]
          [,x (error who "invalid Effect ~s" x)]))
      (define Tail
        (lambda (rp)
          (lambda (tail)
            (match tail
              [(begin ,[Effect -> ef*] ... ,[tail])
               (make-begin `(,ef* ... ,tail))]
              [(if ,[Pred -> pred] ,[conseq] ,[alter])
               `(if ,pred ,conseq ,alter)]
              [(,binop ,[Triv -> triv1] ,[Triv -> triv2]) (guard (binop? binop))
               (make-begin
                `((set! ,return-value-register (,binop ,triv1 ,triv2))
                  (,rp ,frame-pointer-register ,return-value-register)))]
              [(,[Triv -> triv] ,[Triv -> triv*] ...)
               (let ([arg-loc* (param-locations triv*)])
                 (make-begin
                  `((set! ,(reverse arg-loc*) ,(reverse triv*)) ...
                    (set! ,return-address-register ,rp)
                    (,triv ,frame-pointer-register ,return-address-register, arg-loc* ...))))]
              [,triv (guard triv? triv)
                (make-begin `((set! ,return-value-register ,triv)
                              (,rp ,frame-pointer-register ,return-value-register)))]
              [,x (error who "invalid Tail ~s" x)]))))
      (match body
        [(locals (,local* ...) ,tail)
         (let ([rp (unique-name 'rp)]
               [param-loc* (param-locations param*)])
           (let ([tail ((Tail rp) tail)])
             `(locals (,local* ... ,rp ,param* ... ,newframe** ... ...)
                (new-frames ,newframe**
                  ,(make-begin
                    `((set! ,rp ,return-address-register)
                      (set! ,param* ,param-loc*) ...
                      ,tail))))))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,param** ...) ,body*)] ...) ,body)
       `(letrec ([,label* (lambda () ,(map Body body* param**))] ...) ,(Body body '()))]
      [,x (error who "invalid Body ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   uncover-frame-conflict
;
; Description: 
;   Unocovers frame conflicts. Also records call-lives
;   variables and frame locations. Spills contains only
;   the call-live variables. The call-live form contains
;   both spills and frame locations that are live across
;   non tail calls.
;
; Input Language:  
;   Same as the output of impose-calling-conventions
;
; Output Language: 
;   Only change is 
;   Body --> (locals (uvar*)
;              (new-frames (frame*)
;                (spills (uvar*)
;                  (frame-conflict conflict-graph 
;                    (call-live (uvar/fvar*) Tail)))))
;---------------------------------------------------------------
(define-who uncover-frame-conflict
  (define Body
    (lambda (body)
      (define call-live* '())
      (define set-call-live!
        (lambda (live*)
          (set! call-live* (union live* call-live*))))
      (define handle-assignment!
        (lambda (var liveset alist)
          (cond
           [(frame-var? var)
            (set-conflicts! (filter uvar? liveset) alist var)]
           [(uvar? var)
            (let ([row (assq var alist)])
              (set-cdr! row (union liveset (cdr row)))
              (set-conflicts! (filter uvar? liveset) alist var))])))
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
                                      (filter uvar-or-frame-var? `(,triv))
                                      (filter uvar-or-frame-var? loc*))]
            [,x (error who "invalid Tail ~s" x)])))
      (define Pred
        (lambda (pred alist trueset falseset)
          (match pred
            [(true) trueset]
            [(false) falseset]
            [(begin ,ef* ... ,[predset]) (Effect* ef* alist predset)]
            [(if ,pred ,[trueset] ,[falseset]) (Pred pred alist trueset falseset)]
            [(,relop ,triv1 ,triv2)
             (union trueset falseset (filter uvar-or-frame-var? `(,triv1 ,triv2)))]
            [,x (error who "invalid Pred ~s" x)])))
      (define Effect*
        (lambda (ef* alist liveset)
          (match ef*
            [() liveset]
            [(,x* ... (nop)) (Effect* x* alist liveset)]
            [(,x* ... (return-point ,label ,tail))
             (set-call-live! liveset)
             (let ([tailset (Tail tail alist liveset)])
               (Effect* x* alist tailset))]
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
               (Effect* x* alist (union liveset (filter uvar-or-frame-var? `(,triv1 ,triv2)))))]
            [(,x* ... (set! ,var ,triv))
             (let ([liveset (remq var liveset)])
               (handle-assignment! var (remq triv liveset) alist)
               (Effect* x* alist (union liveset (filter uvar-or-frame-var? `(,triv)))))]
            [,x (error who "invalid Effect* ~s" x)])))
      (match body
        [(locals (,uvar* ...)
           (new-frames (,frame* ...) ,tail)) ;; frame* is a set of sets
         (let([fcg* `((,uvar*) ...)])
           (Tail tail fcg* '()) ; neglect the returned liveset
           (let ([spill* (filter uvar? call-live*)])
             `(locals (,(difference uvar* spill*) ...)
                (new-frames (,frame* ...)
                  (spills ,spill*
                    (frame-conflict ,fcg*
                      (call-live ,call-live* ,tail)))))))]
        [,x (error who "invalid Body ~s" x)])))
    (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
(define-who pre-assign-frame
  (define pick-avail
    (lambda (unavail* base)
      (let ([pick (index->frame-var base)])
        (if (not (memq pick unavail*))
            pick
            (pick-avail unavail* (add1 base))))))
  (define select-frames
    (lambda (spill* fcg*)
      (let ([home* '()])
        (map (lambda (spill)
               (let* ([row (assq spill fcg*)]
                      [direct* (filter frame-var? (cdr row))]
                      [indirect* (select-indirect (difference (cdr row) direct*) home*)]
                      [pick (pick-avail (union direct* indirect*) 0)])
                 (set! home* (cons `(,spill ,pick) home*))
                 `(,spill ,pick))) spill*))))
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (new-frames (,frame* ...) ;; frame* is a set of sets
             (spills (,spill* ...)
               (frame-conflict ,fcg*
                 (call-live (,live* ...) ,tail)))))
         (let ([home* (select-frames spill* fcg*)])
           `(locals (,local* ...)
              (new-frames (,frame* ...)
                (locate ,home*
                  (frame-conflict ,fcg*
                    (call-live (,live* ...) ,tail))))))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Input Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) 
;                 (new-frames (frame*)
;                   (locate (home*)
;                     (frame-conflict conflict-graph
;                       (call-live (uvar/fvar*) Tail)))))
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! uvar Triv)               (see implementation)
;            |  (set! uvar (binop Triv Triv))
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv	-->	Var | int | label
;---------------------------------------------------------------
(define-who assign-new-frame
  (define frame-size
    (lambda (live* home*)
      (let f ([live* live*] [max-idx 0])
        (if (null? live*) 
            (add1 max-idx)
            (let ([live-idx (frame-var->index
                             (if (frame-var? (car live*))
                                 (car live*)
                                 (cadr (assq (car live*) home*))))])
              (f (cdr live*) (if (> live-idx max-idx) live-idx max-idx)))))))
  (define Body
    (lambda (body)
      (define newhome* '())
      (define (set-newhome! uvar idx)
        (let ([newhome (index->frame-var idx)])
          (set! newhome* (cons `(,uvar ,newhome) newhome*))))
      (define (assign-homes! newframe** fs)
        (for-each
         (lambda (newframe*)
           (let f ([newframe* newframe*] [idx fs])
             (if (not (null? newframe*))
                 (begin 
                   (set-newhome! (car newframe*) idx)
                   (f (cdr newframe*) (add1 idx))))))
         newframe**))
      (define (Triv t) (if (triv? t) t (error who "invalid Triv ~s" t)))
      (define (Effect fs)
        (lambda (ef)
          (match ef
            [(nop) '(nop)]
            [(begin ,[ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
            [(if ,[(Pred fs) -> pred] ,[conseq] ,[alter])
             `(if ,pred ,conseq ,alter)]
            [(return-point ,label ,tail) 
             (let ([nb (ash fs word-shift)])
               (make-begin
               `((set! ,frame-pointer-register (+ ,frame-pointer-register ,nb))
                 (return-point ,label ,((Tail fs) tail))
                 (set! ,frame-pointer-register (- ,frame-pointer-register ,nb)))))]
            [(set! ,uvar (,binop ,[Triv -> x] ,[Triv -> y]))
             `(set! ,uvar (,binop ,x ,y))]
            ;; uvar may be a newframe uvar
            ;; also triv may be a register since in impose-calling-conventions
            ;; we introduce (set! rp ra) when modifying the head of locals body
            [(set! ,uvar ,triv) 
             `(set! ,uvar ,triv)]
            [,x (error who "invalid Effect ~s" x)])))
      (define (Pred fs)
        (lambda (pred)
          (match pred
            [(true) '(true)]
            [(false) '(false)]
            [(begin ,[(Effect fs) -> ef*] ... ,[pred])
             (make-begin `(,ef* ... ,pred))]
            [(if ,[pred] ,[conseq] ,[alter])
             `(if ,pred ,conseq ,alter)]
            [(,relop ,[Triv -> x] ,[Triv -> y]) `(,relop ,x ,y)]
            [,x (error who "invalid Pred ~s" x)])))
      (define (Tail fs)
        (lambda (tail)
          (match tail
            [(begin ,[(Effect fs) -> ef*] ... ,[tail])
             (make-begin `(,ef* ... ,tail))]
            [(if ,[(Pred fs) -> pred] ,[conseq] ,[alter])
             `(if ,pred ,conseq ,alter)]
            [(,[Triv -> triv] ,loc* ...) ;; loc* may actually contain newframe uvars
               `(,triv ,loc* ...)]
            [,x (error who "invalid Tail ~s" x)])))
      (match body
        [(locals (,local* ...)
           (new-frames (,frame* ...) ;; frame* is a set of sets
             (locate (,home* ...) ;; home* is a set of sets
               (frame-conflict ,fcg*
                 (call-live (,live* ...) ,tail)))))
         (let ([fs (frame-size live* home*)])
           (assign-homes! frame* fs)
           (let([tail ((Tail fs) tail)])
             `(locals (,(difference local* `(,frame* ... ...)) ...)
                (ulocals ()
                  (locate (,home* ... ,newhome* ...)
                    (frame-conflict ,fcg* ,tail))))))]
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
;   Same as the output of finalize-frame-locations
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
            [(begin ,[ef*] ...) (make-begin ef*)]
            [(return-point ,label ,[Tail -> tail]) 
             `(return-point ,label ,tail)])))
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
  (define handle-assignment!
    (lambda (var liveset alist)
      (cond
       [(register? var)
        (set-conflicts! (filter uvar? liveset) alist var)]
       [(uvar? var)
        (let ([row (assq var alist)])
          (set-cdr! row (union liveset (cdr row)))
          (set-conflicts! (filter uvar? liveset) alist var))])))
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
                                  (filter uvar-or-register? `(,triv))
                                  (filter uvar-or-register? loc*))]
        [,x (error who "invalid Tail ~s" x)])))
  (define Pred
    (lambda (pred alist trueset falseset)
      (match pred
        [(true) trueset]
        [(false) falseset]
        [(begin ,ef* ... ,[predset]) (Effect* ef* alist predset)]
        [(if ,pred ,[trueset] ,[falseset]) (Pred pred alist trueset falseset)]
        [(,relop ,triv1 ,triv2)
         (union trueset falseset (filter uvar-or-register? `(,triv1 ,triv2)))]
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
        ;; we have saved all the call-lives and we don't care reg-reg 
        ;; conflicts. So when processing the return point use an 
        ;; empty liveset.
        [(,x* ... (return-point ,label ,tail))
         (let ([tailset (Tail tail alist '())])
           (Effect* x* alist tailset))]
        [(,x* ... (begin ,ef* ...))
         (Effect* `(,x* ... ,ef* ...) alist liveset)]
        [(,x* ... (set! ,var (,binop ,triv1 ,triv2)))
         (let ([liveset (remq var liveset)])
           (handle-assignment! var liveset alist)
           (Effect* x* alist (union liveset (filter uvar-or-register? `(,triv1 ,triv2)))))]
        [(,x* ... (set! ,var ,triv))
         (let ([liveset (remq var liveset)])
           (handle-assignment! var (remq triv liveset) alist)
           (Effect* x* alist (union liveset (filter uvar-or-register? `(,triv)))))]
        [,x (error who "invalid Effect* ~s" x)])))
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (locate ([,uvar* ,fvar*] ...)
               (frame-conflict ,fcg* ,tail))))
         (let ([rcg* `((,local*) ... (,ulocal*) ...)])
           (Tail tail rcg* '()) ; neglect the returned live list
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
  (define triv->fvar
    (lambda (env)
      (lambda (t)
        (if (uvar? t)
            (let ([home (assq t env)])
              (if home (cdr home) t))
            t))))
  (define Pred
    (lambda (env)
      (lambda (pred)
        (match pred
          [(true) '(true)]
          [(false) '(false)]
          [(if ,[(Pred env) -> pred] ,[(Pred env) -> pred1] ,[(Pred env) -> pred2])
           `(if ,pred ,pred1 ,pred2)]
          [(begin ,[(Effect env) -> ef*] ... ,[(Pred env) -> pred])
           (make-begin `(,ef* ... ,pred))]
          [(,relop ,[(triv->fvar env) -> x] ,[(triv->fvar env) -> y])
           `(,relop ,x ,y)]
          [,x (error who "invalid Pred ~s" x)]))))
  (define Effect
    (lambda (env)
      (lambda (ef)
        (match ef
          [(nop) '(nop)]
          [(begin ,[(Effect env) -> ef*] ... ,[(Effect env) -> ef])
           (make-begin `(,ef* ... ,ef))]
          [(if ,[(Pred env) -> pred] ,[(Effect env) -> ef1] , [(Effect env) -> ef2])
           `(if ,pred ,ef1 ,ef2)]
          [(return-point ,label ,[(Tail env) -> tail])
           `(return-point ,label ,tail)]
          ;; Since this comes at least once before select-instructions
          ;; there is no guarantee that x and y will be equal
          [(set! ,[(triv->fvar env) -> x] (,binop ,[(triv->fvar env) -> y] ,[(triv->fvar env) -> z]))
           ;; triv->fvar will resolve a uvar, x, to it's frame location. 
           ;; If x is not a uvar or not assigned frame then it's returned
           ;; as it is.
           `(set! ,x (,binop ,y ,z))]
          [(set! ,[(triv->fvar env) -> x] ,[(triv->fvar env) -> y])
           (if (eq? x y) '(nop) `(set! ,x ,y))]))))
  (define Tail
    (lambda (env)
      (lambda (tail)
        (match tail
          [(begin ,[(Effect env) -> ef*] ... ,[(Tail env) -> tail])
           (make-begin `(,ef* ... ,tail))]
          [(if ,[(Pred env) -> pred] ,[(Tail env) -> tail1] ,[(Tail env) -> tail2])
           `(if ,pred ,tail1 ,tail2)]
          [(,triv ,loc* ...) ;; loc* may actually contain newframe uvars
           (map (triv->fvar env) `(,triv ,loc* ...))]
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
;            |	(return-point label Tail)
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;   Loc   	-->	reg | fvar
;   Var   	-->	uvar | Loc
;   Triv	-->	Var | int | label
;---------------------------------------------------------------
(define-who discard-call-live
  (define (Effect ef)
    (match ef
      [(nop) '(nop)]
      [(begin ,[ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(return-point ,label ,[Tail -> tail])
       `(return-point ,label ,tail)]
      [(set! ,x (,binop ,x ,y)) `(set! ,x (,binop ,x ,y))]
      [(set! ,x ,y) `(set! ,x ,y)]
      [,x (error who "invalid Effect* ~s" x)]))
  (define (Pred pred)
    (match pred
      [(true) '(true)]
      [(false) '(false)]
      [(begin ,[Effect -> ef*] ... ,[pred])
       (make-begin `(,ef* ... ,pred))]
      [(if ,[pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
      [(,relop ,x ,y) `(,relop ,x ,y)]
      [,x (error who "invalid Pred ~s" x)]))
  (define Tail
    (lambda (tail)
      (match tail
        [(if ,[Pred -> pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
        [(begin ,[Effect -> ef*] ... ,[tail]) (make-begin `(,ef* ... ,tail))]
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
;	         |	(return-point label Tail)
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
           (make-begin `(,ef* ... ,pred))]
          [(,relop ,x ,y)
           `(,relop ,(uvar->reg x env) ,(uvar->reg y env))]
          [,x (error who "invalid Pred ~s" x)]))))
  (define Effect
    (lambda (env)
      (lambda (ef)
        (match ef
          [(nop) '(nop)]
          [(begin ,[(Effect env) -> ef*] ... ,[(Effect env) -> ef])
           (make-begin `(,ef* ... ,ef))]
          [(if ,[(Pred env) -> pred] ,[(Effect env) -> ef1] , [(Effect env) -> ef2])
           `(if ,pred ,ef1 ,ef2)]
          [(return-point ,label ,[(Tail env) -> tail])
           `(return-point ,label ,tail)]
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
             (if (eq? x y) '(nop) `(set! ,x ,y)))]))))
  (define Tail
    (lambda (env)
      (lambda (tail)
        (match tail
          [(begin ,[(Effect env) -> ef*] ... ,[(Tail env) -> tail])
           (make-begin `(,ef* ... ,tail))]
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

;---------------------------------------------------------------
; Pass:           
;   expose-frame-var
;
; Description: 
;   Relies on the output of finalize-locations pass and
;   keeps everything the same except frame variables.
;   The frame variables are converted into records of
;   displacement mode operands. The rbp register is
;   the base register in computing the displacements.
;
; Input Language:  
;   Same as the output language of finalize-locations 
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
;   Loc	    -->	reg | fvar -- changed into displacement operands
;   Triv	-->	Loc | int | label
;---------------------------------------------------------------
(define-who expose-frame-var
  (define (Triv offset)
    (lambda (triv)
      (if (frame-var? triv)
          (make-disp-opnd
            frame-pointer-register
            (ash (+ offset (frame-var->index triv)) word-shift))
          triv)))
  (define (Pred offset)
    (lambda (pred)
      (match pred
        [(true) (values '(true) offset)]
        [(false) (values '(false) offset)]
        [(if ,[pred offset] ,conseq ,alter)
         (let-values ([(conseq conseq-offset) ((Pred offset) conseq)]
                      [(alter alter-offset) ((Pred offset) alter)])
           (if (= conseq-offset alter-offset)
               (values `(if ,pred ,conseq ,alter) conseq-offset)
               (error who "offsets for then and else should be equal")))]
        [(begin ,ef* ... ,pred)
         (let ([next-offset offset] [exposed-ef* '()])
           (for-each (lambda (ef)
                       (let-values ([(ef offset) ((Effect next-offset) ef)])
                         (set! exposed-ef* (append exposed-ef* `(,ef)))
                         (set! next-offset offset))) ef*)
           (let-values ([(pred offset) ((Pred next-offset) pred)])
             (values (make-begin `(,exposed-ef* ... ,pred)) offset)))]
        [(,relop ,[(Triv offset) -> x] ,[(Triv offset) -> y])
         (values `(,relop ,x ,y) offset)]
        [,x (error who "invalid Pred ~s" x)])))
  (define (Effect offset)
    (lambda (ef)
      (match ef
        [(nop) (values '(nop) offset)]
        [(begin ,ef* ... ,ef)
         (let ([next-offset offset] [exposed-ef* '()])
           (for-each (lambda (ef)
                       (let-values ([(ef offset) ((Effect next-offset) ef)])
                         (set! exposed-ef* (append exposed-ef* `(,ef)))
                         (set! next-offset offset))) ef*)
           (let-values ([(ef offset) ((Effect next-offset) ef)])
             (values (make-begin `(,exposed-ef* ... ,ef)) offset)))]
        [(if ,[(Pred offset) -> pred offset] ,conseq ,alter)
         (let-values ([(conseq conseq-offset) ((Effect offset) conseq)]
                      [(alter alter-offset) ((Effect offset) alter)])
           (if (= conseq-offset alter-offset)
               (values `(if ,pred ,conseq ,alter) conseq-offset)
               (error who "offsets for then and else should be equal")))]
        [(return-point ,label ,[(Tail offset) -> tail offset])
         (values `(return-point ,label ,tail) offset)] 
        [(set! ,x (,binop ,x ,y)) (guard (eq? frame-pointer-register x))
         (let* ([delta (sra y word-shift)]
                [offset (if (eq? binop '+) (- offset delta) (+ offset delta))])
           (values `(set! ,x (,binop ,x ,y)) offset))] 
        [(set! ,[(Triv offset) -> x] (,binop ,[(Triv offset) -> x] ,[(Triv offset) -> y]))
         (values `(set! ,x (,binop ,x ,y)) offset)]
        [(set! ,[(Triv offset) -> x] ,[(Triv offset) -> y])
         (values `(set! ,x ,y) offset)])))
  (define (Tail offset)
    (lambda (tail)
      (match tail
        [(begin ,ef* ... ,tail)
         (let ([next-offset offset] [exposed-ef* '()])
           (for-each (lambda (ef)
                       (let-values ([(ef offset) ((Effect next-offset) ef)])
                         (set! exposed-ef* (append exposed-ef* `(,ef)))
                         (set! next-offset offset))) ef*)
           (let-values ([(tail offset) ((Tail next-offset) tail)])
             (values (make-begin `(,exposed-ef* ... ,tail)) offset)))]
        [(if ,[(Pred offset) -> pred next-offset] ,conseq ,alter)
         (let-values ([(conseq conseq-offset) ((Tail next-offset) conseq)]
                      [(alter alter-offset) ((Tail next-offset) alter)])
           (if (= conseq-offset alter-offset)
               (values `(if ,pred ,conseq ,alter) conseq-offset)
               (error who "offsets for then and else should be equal")))]
        [(,[(Triv offset) -> triv]) (values `(,triv) offset)]
        [,x (error who "invalid Tail ~s" x)])))
  (lambda (s)
    (match s
      ;; discard the returned offset values
      [(letrec ([,label* (lambda () ,[(Tail 0) -> tail* offset*])] ...) ,[(Tail 0) -> tail offset])
       `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)]
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
      [(,x* ... (return-point ,label ,[Tail -> tail tb*]))
       (let-values ([(x xb*) (Effect* x* `(,tail))])
         (values x
                 `(,xb* ... ,tb* ...
                    [,label (lambda () ,(make-begin tail*))])))]

      ; no need to handle ending effect separately or 
      ; even effects before and after begin separately
      ; since we have verified the source already. So
      ; we know all these x* and ef* are just effects.
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
