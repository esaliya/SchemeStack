; Saliya Ekanayake
; sekanaya
; Assignment 8

;---------------------------------------------------------------
; Overall Strategy:
;
;                      verify-uil
;                          |
;                 remove-complex-opera*
;                          |
;                     flatten-set!
;                          |
;             {impose-calling-conventions}
;                          |
;             <<expose-allocation-pointer>>
;                          |
;                uncover-frame-conflict
;                          |
;                  [pre-assign-frame]
;                          |
;                   assign-new-frame
;                          |
;               finalize-frame-locations  <----------
;                          |                        |
;                {select-instructions}              |
;                          |                        |
;              uncover-register-conflict            |
;                          |                        |
;                  [assign-registers]               |
;                          |                        |
;                  [everybody-home?]                |
;                     /         \                   |
;                Yes /           \ No               |
;                   /             \                 |
;          discard-call-live  [assign-frame] --------
;                  |
;          finalize-locations
;                  |
;           expose-frame-var
;                  |
;      <<expose-memory-operands>>
;                  |
;         [expose-basic-block]
;                  |
;          [flatten-program]
;                  |
;          [generate-x86-64]
;
;   Passes marked inside square brackets are taken unchanged
;   from previous time. The ones in angle brackets, i.e. <<...>>
;   are new to this assignment. The ones in curly brackets 
;   undergo minor modifications. The rest of the passes are
;   updated trivially to handle the new operations.
;
; verify-uil, remove-complex-opera*, flatten-set!
;   Direct modifications to handle the new alloc, mref, and 
;   mset! forms.
;
; impose-calling-conventions
;   Obviously adds match clauses to handle the new operations.
;   The alloc and mref in Tail context are handled similar to
;   the binop case, i.e. value of the operation is stored in
;   return-value-register and jumps to the return-pointer.
;   The alloc, mref, and mset! in Effect context are handled
;   similar to set! with binop case. 
; 
;   Also, this now marks allocation-pointer-register as live
;   in each call.
;
; expose-allocation-pointer
;   This simply replaces the alloc in Effect context by two 
;   set! operations. The first one simply sets the orignal
;   LHS variable to the value of allocation-pointer-register.
;   The second one increments the allocation-pointer-register
;   by the given value.
;
; uncover-frame-conflict, assign-new-frame, finalize-frame-locations
;   These undergo trivial additions of match clauses to handle
;   mref and mset! in Effect context.
;
; select-instructions
;   This pass now handles the two memory operations, i.e. mref
;   and mset!. These memory operands should eventually be 
;   converted into index mode operands in x86_64 assembly code.
;   To do this, this pass should assign the base and offset
;   values of these two operations into registers. It does so
;   by introducing unspillables, which will get registers in 
;   assign-register pass. If the value in mset! or the LHS 
;   variable in mref are not unspillables (i.e. no guarantee
;   to get a register eventually) then they are assigned to
;   new unspillable variables as well. It is possible to 
;   generate incorrect memory to memory move if this is not 
;   handled properly.
;
; uncover-register-conflict, discard-call-live,
; finalize-locations, expose-frame-var
;   These undergo trivial additions of match clauses to handle
;   mref and mset! in Effect context.
;
; expose-memory-operands
;   This pass simply creates index operands for mref and mset!
;   Effect context. The final assembly code generation is
;   guranteed to hold the x86_64 constraints since the 
;   select-instruction pass make sure on that. 
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass: verify-uil (modified the given one in assignment 7)
;---------------------------------------------------------------
;;; Andy Keep, Kent Dybvig
;;; P423/P523
;;; Spring 2010

;;; verify-scheme accepts a single value and verifies that the value
;;; is a valid program in the current source language.
;;;
;;; Grammar for verify-scheme (assignment 8):
;;;
;;;  Program --> (letrec ([<label> (lambda (<uvar>*) <Body>)]*) <Body>)
;;;  Body    --> (locals (<uvar>*) <Tail>)
;;;  Tail    --> <Triv>
;;;           |  (alloc <Value>)
;;;           |  (mref <Value> <Value>)
;;;           |  (binop <Value> <Value>)
;;;           |  (<Value> <Value>*)
;;;           |  (if <Pred> <Tail> <Tail>)
;;;           |  (begin <Effect>* <Tail>)
;;;  Pred    --> (true)
;;;           |  (false)
;;;           |  (<relop> <Value> <Value>)
;;;           |  (if <Pred> <Pred> <Pred>)
;;;           |  (begin <Effect>* <Pred>)
;;;  Effect  --> (nop)
;;;           |  (mset! <Value> <Value> <Value>)
;;;           |  (set! <uvar> <Value>)
;;;           |  (<Value> <Value>*)
;;;           |  (if <Pred> <Effect> <Effect>)
;;;           |  (begin <Effect>* <Effect>)
;;;  Value   --> <Triv>
;;;           |  (alloc <Value>)
;;;           |  (mref <Value> <Value>)
;;;           |  (<binop> <Value> <Value>)
;;;           |  (<Value> <Value>*)
;;;           |  (if <Pred> <Value> <Value>)
;;;           |  (begin <Effect>* <Value>)
;;;  Triv    --> <uvar> | <integer> | <label>
;;;
;;; Where uvar is symbol.n, n >= 0
;;;       binop is mref, +, -, *, logand, logor, or sra
;;;       relop is <, <=, =, >=, >
;;;       label is symbol$n, n >= 0
;;;
;;; Machine constraints:
;;;   - sra's second oeprand must be an exact integer k, 0 <= k <= 63
;;;   - each other integer must be a exact integer n, -2^63 <= n <= 2^63-1
;;;
;;; If the value is a valid program, verify-scheme returns the value
;;; unchanged; otherwise it signals an error.
(define-who verify-uil
  (define binops '(+ - * logand logor sra))
  (define relops '(< > <= >= =))
  (define verify-x-list
    (lambda (x* x? what)
      (let loop ([x* x*] [idx* '()])
        (unless (null? x*)
          (let ([x (car x*)] [x* (cdr x*)])
            (unless (x? x)
              (error who "invalid ~s ~s found" what x))
            (let ([idx (extract-suffix x)])
              (when (member idx idx*)
                (error who "non-unique ~s suffix ~s found" what idx))
              (loop x* (cons idx idx*))))))))
  (define Triv
    (lambda (label* uvar*)
      (lambda (t)
        (unless (or (label? t) (uvar? t) (and (integer? t) (exact? t)))
          (error who "invalid Triv ~s" t))
        (when (and (integer? t) (exact? t))
          (unless (int64? t)
            (error who "integer out of 64-bit range ~s" t)))
        (when (uvar? t)
          (unless (memq t uvar*)
            (error who "reference to unbound uvar ~s" t)))
        (when (label? t)
          (unless (memq t label*)
            (error who "unbound label ~s" t)))
        (values))))
  (define Value
    (lambda (label* uvar*)
      (lambda (val)
        (match val
          [(if ,[(Pred label* uvar*) ->] ,[] ,[]) (values)]
          [(begin ,[(Effect label* uvar*) ->] ... ,[]) (values)]
          [(sra ,[] ,y)
           (unless (uint6? y)
             (error who "invalid sra operand ~s" y))
           (values)]
          [(alloc ,[]) (values)]
          [(mref ,[] ,[]) (values)]
          [(,binop ,[] ,[])
           (guard (memq binop binops))
           (values)]
          [(,[] ,[] ...) (values)]
          [,[(Triv label* uvar*) ->] (values)]))))
  (define Effect
    (lambda (label* uvar*)
      (lambda (ef)
        (match ef
          [(nop) (values)]
          [(if ,[(Pred label* uvar*) ->] ,[] ,[]) (values)]
          [(begin ,[] ... ,[]) (values)]
          [(set! ,var ,[(Value label* uvar*) ->])
           (unless (memq var uvar*)
             (error who "assignment to unbound var ~s" var))
           (values)]
          [(mset! ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->])
           (values)]
          [(,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->] ...) (values)]
          [,ef (error who "invalid Effect ~s" ef)]))))
  (define Pred
    (lambda (label* uvar*)
      (lambda (pr)
        (match pr
          [(true) (values)]
          [(false) (values)]
          [(if ,[] ,[] ,[]) (values)]
          [(begin ,[(Effect label* uvar*) ->] ... ,[]) (values)]
          [(,relop ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->])
           (guard (memq relop relops))
           (values)]
          [,pr (error who "invalid Pred ~s" pr)]))))
  (define Tail
    (lambda (label* uvar*)
      (lambda (tail)
        (match tail
          [(if ,[(Pred label* uvar*) ->] ,[] ,[]) (values)]
          [(begin ,[(Effect label* uvar*) ->] ... ,[]) (values)]
          [(sra ,[(Value label* uvar*) ->] ,y)
           (unless (uint6? y)
             (error who "invalid sra operand ~s" y))
           (values)]
          [(alloc ,[(Value label* uvar*) ->]) (values)]
          [(mref ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->]) (values)]
          [(,binop ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->])
           (guard (memq binop binops))
           (values)]
          [(,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->] ...) (values)]
          [,[(Triv label* uvar*) ->] (values)]))))
  (define Body
    (lambda (label* fml*)
      (lambda (x)
        (match x
          [(locals (,local* ...) ,tail)
           (let ([uvar* `(,fml* ... ,local* ...)])
             (verify-x-list uvar* uvar? 'uvar)
             ((Tail label* uvar*) tail)
             (values))]
          [,x (error who "invalid Body ~s" x)]))))
  (define Lambda
    (lambda (label*)
      (lambda (x)
        (match x
          [(lambda (,fml* ...) ,[(Body label* fml*) ->]) (values)]
          [,x (error who "invalid Lambda ~a" x)]))))
  (lambda (x)
    (match x
      [(letrec ([,label* ,[(Lambda label*) ->]] ...) ,[(Body label* '()) ->])
       (verify-x-list label* label? 'label)]
      [,x (error who "invalid Program ~s" x)])
    x))
;---------------------------------------------------------------

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
;	         |	(alloc Value)
;	         |	(mref Value Value)
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
;	         |	(mset! Value Value Value)
;            |  (Value Value*)
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;  Value	-->	Triv
;	         |	(alloc Value)
;	         |	(mref Value Value)
;	         |	(binop Value Value)
;            |  (Value Value*)
;	         |	(if Pred Value Value)
;	         |	(begin Effect* Value)
;   Triv	-->	uvar | int | label 
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
;   Tail	-->	Triv
;	         |	(alloc Triv)
;	         |	(mref Triv Triv)
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
;	         |	(mset! Triv Triv Triv)
;            |  (Triv Triv*)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;  Value	-->	Triv
;	         |	(alloc Triv)
;	         |	(mref Triv Triv)
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
         (values `(,s ,rest* ...) set*)]
        [(,[Value -> expr] . ,[rest* set*])
         (let ([t (new-t)])
           (values `(,t ,rest* ...) `((set! ,t ,expr) ,set* ...)))]
        [,expr* (error who "invalid Expr ~s" expr*)]))
    (define (simple? x)
      (or (uvar? x) (label? x) (and (integer? x) (exact? x))
          (memq x '(+ - * logand logor sra)) (memq x '(= < <= > >=))
          (memq x '(alloc mref mset!))))
    (define (triv? x) (or (uvar? x) (int64? x) (label? x)))
    (define (Value val)
      (match val
        [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[val]) (make-begin `(,ef* ... ,val))]
        [(alloc ,n) (trivialize-call `(alloc ,n))]
        [(mref ,b ,o) (trivialize-call `(mref ,b ,o))]
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
        [(mset! ,b ,o ,v) (trivialize-call `(mset! ,b ,o ,v))]
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
      (match tail
        [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[tail]) (make-begin `(,ef* ... ,tail))]
        [(alloc ,n) (trivialize-call `(alloc ,n))]
        [(mref ,b ,o) (trivialize-call `(mref ,b ,o))]
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
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
;   Tail	-->	Triv
;	         |	(alloc Triv)
;	         |	(mref Triv Triv)
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
;	         |	(mset! Triv Triv Triv)
;            |  (Triv Triv*)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;  Value	-->	Triv
;	         |	(alloc Triv)
;	         |	(mref Triv Triv)
;			 |	(binop Triv Triv)
;			 |	(if Pred Value Value)
;			 |	(begin Effect* Value)
;            |  (Triv Triv*)
;   Triv	-->	uvar | int | label
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
;   Tail	-->	Triv
;	         |	(alloc Triv)
;	         |	(mref Triv Triv)
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
;	         |	(set! uvar (alloc Triv))
;	         |	(set! uvar (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
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
        [(alloc ,n) `(set! ,uvar (alloc ,n))]
        [(mref ,b ,o) `(set! ,uvar (mref ,b ,o))]
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
        [(mset! ,b ,o ,v) `(mset! ,b ,o ,v)]
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
        [(mref ,b ,o) `(mref ,b ,o)]
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
;   Also, this pass will add allocation-pointer-register as
;   live in each call
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
;   Tail	-->	Triv
;	         |	(alloc Triv)
;	         |	(mref Triv Triv)
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
;	         |	(set! uvar (alloc Triv))
;	         |	(set! uvar (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (Triv Triv*)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Triv	-->	uvar | int | label
;
; Output Language:
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body	-->	(locals (uvar*) (new-frames (Frame*) Tail))
;   Frame   --> (uvar*)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (alloc Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
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
      (define Pred
        (lambda (pred)
          (match pred
            [(true) '(true)]
            [(false) '(false)]
            [(if ,[pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
            [(begin ,[Effect -> ef*] ... ,[pred]) (make-begin `(,ef* ... ,pred))]
            [(,relop ,[Triv -> x] ,[Triv -> y]) `(,relop ,x ,y)]
            [,x (error who "invalid Pred ~s" x)])))
      (define Effect
        (lambda (ef)
          (match ef
            [(nop) '(nop)]
            [(if ,[Pred -> pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
            [(begin ,[ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
            [(set! ,uvar (alloc ,[Triv -> n]))
             `(set! ,uvar (alloc ,n))]
            [(set! ,uvar (mref ,[Triv -> b] ,[Triv -> o]))
             `(set! ,uvar (mref ,b ,o))]
            [(mset! ,[Triv -> b] ,[Triv -> o] ,[Triv -> v])
             `(mset! ,b ,o ,v)]
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
                                   (,rator ,frame-pointer-register ,return-address-register 
                                    ,allocation-pointer-register ,nt-arg-loc* ...)))))]
            [,x (error who "invalid Effect ~s" x)])))
      (define Tail
        (lambda (rp)
          (lambda (tail)
            (match tail
              [(begin ,[Effect -> ef*] ... ,[tail])
               (make-begin `(,ef* ... ,tail))]
              [(if ,[Pred -> pred] ,[conseq] ,[alter])
               `(if ,pred ,conseq ,alter)]
              [(alloc ,[Triv -> n]) 
               (make-begin
                 `((set! ,return-value-register (alloc ,n))
                   (,rp ,frame-pointer-register ,return-value-register ,allocation-pointer-register)))]
              [(mref ,[Triv -> b] ,[Triv -> o])
               (make-begin
                 `((set! ,return-value-register (mref ,b ,o))
                   (,rp ,frame-pointer-register ,return-value-register ,allocation-pointer-register)))]
              [(,binop ,[Triv -> triv1] ,[Triv -> triv2]) (guard (binop? binop))
               (make-begin
                `((set! ,return-value-register (,binop ,triv1 ,triv2))
                  (,rp ,frame-pointer-register ,return-value-register ,allocation-pointer-register)))]
              [(,[Triv -> triv] ,[Triv -> triv*] ...)
               (let ([arg-loc* (param-locations triv*)])
                 (make-begin
                  `((set! ,(reverse arg-loc*) ,(reverse triv*)) ...
                    (set! ,return-address-register ,rp)
                    (,triv ,frame-pointer-register ,return-address-register 
                      ,allocation-pointer-register ,arg-loc* ...))))]
              [,triv (guard triv? triv)
                (make-begin
                  `((set! ,return-value-register ,triv)
                    (,rp ,frame-pointer-register ,return-value-register, allocation-pointer-register)))]
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
;   expose-allocation-pointer
;
; Description: 
;   This pass removes the allocation effect by introducing
;   a set! effect to modify the allocation-pointer-register.
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body	-->	(locals (uvar*) (new-frames (Frame*) Tail))
;   Frame   --> (uvar*)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (alloc Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;
; Output Language:  
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body	-->	(locals (uvar*) (new-frames (Frame*) Tail))
;   Frame   --> (uvar*)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;---------------------------------------------------------------
(define-who expose-allocation-pointer
  (define (Effect ef)
    (match ef
      [(nop) '(nop)]
      [(begin ,[ef*] ... ,[ef])
       (make-begin `(,ef* ... ,ef))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(return-point ,label ,[Tail -> tail])
       `(return-point ,label ,tail)]
      [(mset! ,b ,o ,v) `(mset! ,b ,o ,v)]
      [(set! ,x (alloc ,n))
       (make-begin
         `((set! ,x ,allocation-pointer-register)
           (set! ,allocation-pointer-register (+ ,allocation-pointer-register ,n))))]
      [(set! ,x (mref ,b ,o)) `(set! ,x (mref ,b ,o))]
      [(set! ,x (,binop ,y ,z)) `(set! ,x (,binop ,y ,z))]
      [(set! ,x ,y) `(set! ,x ,y)]
      [,x (error who "invalid Effect ~s" x)]))
  (define (Pred pred)
    (match pred
      [(true) '(true)]
      [(false) '(false)]
      [(begin ,[Effect -> ef*] ... ,[pred])
       (make-begin `(,ef* ... ,pred))]
      [(if ,[pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(,relop ,x ,y) `(,relop ,x ,y)]
      [,x (error who "invalid Pred ~s" x)]))
  (define (Tail tail)
    (match tail
      [(begin ,[Effect -> ef*] ... ,[tail])
       (make-begin `(,ef* ... ,tail))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(,triv ,loc* ...) `(,triv ,loc* ...)]
      [,x (error who "invalid Tail ~s" x)]))
  (define (Body body)    
    (match body
      [(locals (,local* ...)
         (new-frames (,frame* ...) ,[Tail -> tail]))
       `(locals (,local* ...)
          (new-frames (,frame* ...) ,tail))]
      [,x (error who "invalid Body ~s" x)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
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
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body	-->	(locals (uvar*) (new-frames (Frame*) Tail))
;   Frame   --> (uvar*)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;
; Output Language: 
;   Note. Only Body form is changed.
;
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body --> (locals (uvar*)
;              (new-frames (Frame*)
;                (spills (uvar*)
;                  (frame-conflict conflict-graph 
;                    (call-live (uvar/fvar*) Tail)))))
;   Frame   --> (uvar*)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
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
            [(,x* ... (set! ,var (mref ,b ,o)))
             (let ([liveset (remq var liveset)])
               (handle-assignment! var liveset alist)
               (Effect* x* alist (union liveset (filter uvar-or-frame-var? `(,b ,o)))))]
            [(,x* ... (mset! ,b ,o ,v))
             (Effect* x* alist (union liveset (filter uvar-or-frame-var? `(,b ,o ,v))))]
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
; Pass:           
;   pre-assign-frame
;
; Description: 
;   Assigns frame homes for the set of spills. It discards the
;   spills form from the output. Spills are the set of call-live
;   variables that we want to push on to the frame stack. It 
;   introduces the locate form including the assigned frame homes.
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                (new-frames (Frame*)
;                  (spills (uvar*)
;                    (frame-conflict conflict-graph 
;                      (call-live (uvar/fvar*) Tail)))))
;   Frame   --> (uvar*)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;
; Output Language: 
;   Note. Only Body form is changed.

;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                (new-frames (Frame*)
;                  (locate ([uvar fvar]*)
;                    (frame-conflict conflict-graph 
;                      (call-live (uvar/fvar*) Tail)))))
;   Frame   --> (uvar*)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
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
; Pass:           
;   assign-new-frame
;
; Description: 
;   Determines the size of each body's frame. The size is
;   calculated by first finding the maximum frame index of the 
;   call-live variables (Note. In the previous step of 
;   pre-assign-frame all the call-live variables are assigned 
;   with frame variables.) and frame variables. The frame size
;   is simply one more than the maximum frame index.
;
;   Then it assigns frame locations with indices starting from
;   frame size for each outgoing sequence of new-frame variables.
;   These assignments are recorded in the locate form along with 
;   the existing assignments. 
;
;   It also increments and decrements the frame pointer around 
;   each return-point form. The increment/decrement value is
;   calculated by multiplying frame size by word size.
;
;   This pass discards the new-frames form and call-live form. 
;   It also removes the new-frame variables from the locals form.
;   Additionally it introduces the ulocals form for the sake of
;   following passes.
;
;   Note. In this pass we could have calculated the frame size 
;   for each non tail call. At this point, however, we move
;   ahead with one size fits all approach.
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                (new-frames (Frame*)
;                  (locate ([uvar fvar]*)
;                    (frame-conflict conflict-graph 
;                      (call-live (uvar/fvar*) Tail)))))
;   Frame   --> (uvar*)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                (ulocals ()
;                  (locate ([uvar fvar]*)
;                    (frame-conflict conflict-graph Tail))))
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
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
            [(mset! ,b ,o ,v) `(mset! ,b ,o ,v)]
            [(set! ,var (mref ,b ,o)) `(set! ,var (mref ,b ,o))]            
            [(set! ,x (,binop ,y ,z)) `(set! ,x (,binop ,y ,z))]
            [(set! ,x ,y) `(set! ,x ,y)]
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
            [(,relop ,x ,y) `(,relop ,x ,y)]
            [,x (error who "invalid Pred ~s" x)])))
      (define (Tail fs)
        (lambda (tail)
          (match tail
            [(begin ,[(Effect fs) -> ef*] ... ,[tail])
             (make-begin `(,ef* ... ,tail))]
            [(if ,[(Pred fs) -> pred] ,[conseq] ,[alter])
             `(if ,pred ,conseq ,alter)]
            ;; loc* may actually contain newframe uvars
            [(,triv ,loc* ...) `(,triv ,loc* ...)]
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
;   finalize-frame-locations
;
; Description: 
;   This is the start of the iterating phase. It will replaces 
;   each occurence of frame assigned variables with the 
;   corresponding frame for incomplete Body forms. For complete
;   Body forms it returns them as they are.
;
; Input Language:
;   Note. The only difference from the output of assign-new-frame
;   is that there may be uvars in the ulocals form as a result of 
;   a previous iteration. Also it is possible that some Body forms
;   to be complete.
;   
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                 (ulocals (uvar*)
;                   (locate ([uvar fvar]*)
;                     (frame-conflict conflict-graph Tail))))
;            |  (locate ([uvar fvar]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;
; Output Language:
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                 (ulocals (uvar*)
;                   (locate ([uvar fvar]*)
;                     (frame-conflict conflict-graph Tail))))
;            |  (locate ([uvar fvar]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
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
          [(mset! ,[(triv->fvar env) -> b] ,[(triv->fvar env) -> o] ,[(triv->fvar env) -> v])
           `(mset! ,b ,o ,v)]
          [(set! ,[(triv->fvar env) -> x] (mref ,[(triv->fvar env) -> b] ,[(triv->fvar env) -> o]))
           `(set! ,x (mref ,b ,o))]
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
;   select-instructions
;
; Description: 
;   Corrects any invalid, w.r.t. x84_64 architecture, effect.
;   Possibly introduce unspillables in the ulocals form. Also,
;   this will assign the base and offset of each mref and mset! 
;   operations to unspillables, which should be a given a 
;   register. This is necessary since we eventually needs to 
;   create a displacement operand for the mref and mset! 
;   operations and doing so will require us to have a base register.
;
; Input:
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                 (ulocals (uvar*)
;                   (locate ([uvar fvar]*)
;                     (frame-conflict conflict-graph Tail))))
;            |  (locate ([uvar fvar]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;
; Output:
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                 (ulocals (uvar*)
;                   (locate ([uvar fvar]*)
;                     (frame-conflict conflict-graph Tail))))
;            |  (locate ([uvar fvar]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
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
      (define (Pred ulocal*)
        (lambda (pred)
          (match pred
            [(true) '(true)]
            [(false) '(false)]
            [(if ,[pred] ,[conseq] ,[alter])
             `(if ,pred ,conseq ,alter)]
            [(begin ,[(Effect ulocal*) -> ef*] ... ,[pred])
             (make-begin `(,ef* ... ,pred))]
            [(,relop ,x ,y) (Relop `(,relop ,x ,y))]
            [,x (error who "invalid Pred ~s" x)])))
      (define (Effect ulocal*)
        (lambda (ef)
          (match ef
            [(nop) '(nop)]
            [(if ,[(Pred ulocal*) -> pred] ,[conseq] ,[alter])
             `(if ,pred ,conseq ,alter)]
            [(begin ,[ef*] ...) (make-begin ef*)]
            [(return-point ,label ,[(Tail ulocal*) -> tail]) 
             `(return-point ,label ,tail)]
            [(mset! ,b ,o ,v) (MemOp `(mset! ,b ,o ,v) ulocal*)]
            [(set! ,x (mref ,b ,o)) (MemOp `(set! ,x (mref ,b ,o)) ulocal*)] 
            [(set! ,x (,binop ,y ,z)) (Binop `(set! ,x (,binop ,y ,z)))]
            [(set! ,x ,y) (Move `(set! ,x ,y))])))
      (define (Tail ulocal*)
        (lambda (tail)
          (match tail
            [(begin ,[(Effect ulocal*) -> ef*] ... ,[(Tail ulocal*) -> tail])
             (make-begin `(,ef* ... ,tail))]
            [(if ,[(Pred ulocal*) -> pred] ,[conseq] ,[alter])
             `(if ,pred ,conseq ,alter)]
            [(,triv ,loc* ...) `(,triv ,loc* ...)]
            [,x (error who "invalid Tail ~s" x)])))
      (define MemOp
        (lambda (memop ulocal*)
          (match memop
            [(mset! ,b ,o ,v)
             (let ([ub (if (not (memq b ulocal*)) (newu) b)]
                   [uo (if (not (memq o ulocal*)) (newu) o)]
                   [uv (if (not (memq v ulocal*)) (newu) v)])
               ;; some operations may result nop's, which will 
               ;; eventually get wiped away by expose-basic-block
               (make-begin
                 `((set! ,ub ,b)
                   (set! ,uo ,o)
                   (set! ,uv ,v)
                   (mset! ,ub ,uo ,uv))))]
            [(set! ,x (mref ,b ,o))
             (let ([ub (if (not (memq b ulocal*)) (newu) b)]
                   [uo (if (not (memq o ulocal*)) (newu) o)]
                   [ux (if (not (memq x ulocal*)) (newu) x)])
               ;; some operations may result nop's, which will 
               ;; eventually get wiped away by expose-basic-block
               (make-begin
                 `((set! ,ub ,b)
                   (set! ,uo ,o)
                   (set! ,ux (mref ,ub ,uo))
                   (set! ,x ,ux))))])))
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
                     (frame-conflict ,fcg* ,tail))))
         (let ([tail ((Tail ulocal*) tail)])
           `(locals (,local* ...)
              (ulocals (,ulocal* ... ,newulocal* ...)
                (locate ([,uvar* ,fvar*] ...)
                        (frame-conflict ,fcg* ,tail)))))] 
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
;   Unocovers register conflicts and marks them in the
;   register-conflict form as a conflict-graph. If the Body
;   form is complete, however, then it will pass it as it is
;   without any modification.
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                 (ulocals (uvar*)
;                   (locate ([uvar fvar]*)
;                     (frame-conflict conflict-graph Tail))))
;            |  (locate ([uvar fvar]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;	              (ulocals (uvar*)
;		            (locate ([uvar fvar]*)
;		              (frame-conflict conflict-graph
;		                (register-conflict conflict-graph Tail)))))
;    	     |  (locate ([uvar Loc]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
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
        [(,x* ... (mset! ,b ,o ,v))
         (Effect* x* alist (union liveset (filter uvar-or-register? `(,b ,o ,v))))]
        [(,x* ... (set! ,var (mref ,b ,o)))
         (let ([liveset (remq var liveset)])
           (handle-assignment! var liveset alist)
           (Effect* x* alist (union liveset (filter uvar-or-register? `(,b ,o)))))]
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
;   assign-registers
;
; Description: 
;   Tries to assign registers for all the spillables and 
;   unspillables. If successful it will create a complete
;   Body form. If unsuccessful it will NOT record the 
;   possible assignments in the locate form. Also, it does
;   NOT change the set of unspillables. However, it will 
;   record the set of spills in the spills form. These 
;   spills are removed from the original list of spillables
;   (i.e. the ones inside locals form).
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;	              (ulocals (uvar*)
;		            (locate ([uvar fvar]*)
;		              (frame-conflict conflict-graph
;		                (register-conflict conflict-graph Tail)))))
;    	     |  (locate ([uvar Loc]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;		          (ulocals (uvar*)
;		            (spills (uvar*)
;		              (locate ([uvar fvar]*)
;		                (frame-conflict conflict-graph Tail)))))
;    	     |	(locate ([uvar Loc]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;---------------------------------------------------------------
(define-who assign-registers
  (define reglen (lambda () (length registers)))
  (define pick-if
    (lambda (pred? cg)
      (cond
       [(null? cg) #f]
       [(pred? (car cg)) (car cg)]
       [else (pick-if pred? (cdr cg))])))
  (define low-degree?
    (lambda (row)
      (< (sub1 (length row)) (reglen))))
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
                 [(pickregs) (filter register? (cdr pick))] ; registers in picked row
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
;   everybody-home
;
; Description: 
;   Checks if all the body elements have gone through the
;   register/frame allocator completely. If this is the case
;   then every Body form should be complete and the program 
;   will be passed on to the next pass (i.e. discard-call-live).
;   If at least one incomplete Body form is found the program
;   will be passed on to assign-frame which will assign frames
;   for the spills and push the program back into the iteration
;   starting with finalize-frame-locations.
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;		          (ulocals (uvar*)
;		            (spills (uvar*)
;		              (locate ([uvar fvar]*)
;		                (frame-conflict conflict-graph Tail)))))
;    	     |	(locate ([uvar Loc]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
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
; Pass:           
;   assign-frame
;
; Description: 
;   Assign frames for spilled variables.
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;		          (ulocals (uvar*)
;		            (spills (uvar*)
;		              (locate ([uvar fvar]*)
;		                (frame-conflict conflict-graph Tail)))))
;    	     |	(locate ([uvar Loc]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;		          (ulocals (uvar*)
;		            (locate ([uvar fvar]*)
;		              (frame-conflict conflict-graph Tail))))
;	         |  (locate ([uvar Loc]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label
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
                    [direct* (filter frame-var? (cdr row))]
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
;   discard-call-live
;
; Description: 
;   This pass simply discards the Loc* in tail calls. The rest 
;   is kept as it is.
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;		          (ulocals (uvar*)
;		            (spills (uvar*)
;		              (locate ([uvar fvar]*)
;		                (frame-conflict conflict-graph Tail)))))
;    	     |	(locate ([uvar Loc]*) Tail)
;   Tail	-->	(Triv Loc*)
;			 |	(if Pred Tail Tail)
;			 |	(begin Effect* Tail)
;   Pred	-->	(true)
;			 |	(false)
;			 |	(relop Triv Triv)
;			 |	(if Pred Pred Pred)
;			 |	(begin Effect* Pred)
;   Effect	-->	(nop)
;			 |	(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |  (return-point label Tail)
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Var	    -->	uvar | Loc
;   Triv    -->	Var | int | label 
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
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
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
      [(mset! ,b ,o ,v) `(mset! ,b ,o ,v)]
      [(set! ,x (mref ,b ,o)) `(set! ,x (mref ,b ,o))]
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
;   Replaces location aliases with the actual register
;   variable. It also discards the locate form presented
;   in the input grammer. 
;
; Input Language:  
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
;	         |	(set! Var (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;            |	(return-point label Tail)
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;   Loc   	-->	reg | fvar
;   Var   	-->	uvar | Loc
;   Triv	-->	Var | int | label
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
;	         |	(set! Loc (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
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
          [(mset! ,b ,o ,v) 
           (let ([b (uvar->reg b env)] [o (uvar->reg o env)] [v (uvar->reg v env)])
             `(mset! ,b ,o ,v))]
          [(set! ,x (mref ,b ,o))
           (let ([x (uvar->reg x env)] [b (uvar->reg b env)] [o (uvar->reg o env)])
             `(set! ,x (mref ,b ,o)))]
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
;   Keeps everything the same except for frame variables.
;   The frame variables are converted into records of
;   displacement mode operands. The frame-pointer-register 
;   is the base register in computing the displacements.
;
; Input Language:  
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
;	         |	(set! Loc (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;	         |	(return-point label Tail)
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;   Loc	    -->	reg | fvar
;   Triv	-->	Loc | int | label 
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
;	         |	(set! Loc (mref Triv Triv))
;	         |	(return-point label Tail)
;	         |	(mset! Triv Triv Triv)
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;   Loc	    -->	reg | disp-opnd
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
        [(mset! ,[(Triv offset) -> b] ,[(Triv offset) -> o] ,[(Triv offset) -> v])
         (values `(mset! ,b ,o ,v) offset)]
        [(set! ,[(Triv offset) -> x] (mref ,[(Triv offset) -> b] ,[(Triv offset) -> o]))
         (values `(set! ,x (mref ,b ,o)) offset)]
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
;   expose-memory-operands
;
; Description: 
;   Keeps everything the same except to introduce index
;   operands for mref and mset!. The base and offset values
;   of each of these are guaranteed to be marked to be placed 
;   in a register by select-instruction pass. Also since the
;   program came to this pass it guarantees that base and offset
;   are assigned register homes by assign-register pass.
;   This pass will use the particular registers when creating 
;   the index mode operand.
;
; Input Language:  
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
;	         |	(set! Loc (mref Triv Triv))
;	         |	(mset! Triv Triv Triv)
;	         |	(return-point label Tail)
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;   Loc	    -->	reg | disp-opnd
;   Triv	-->	Loc | int | label 
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
;   Loc	    -->	reg | disp-opnd | index-opnd
;   Triv	-->	Loc | int | label
;---------------------------------------------------------------
(define-who expose-memory-operands
  (define (Effect ef)
    (match ef
      [(nop) '(nop)]
      [(begin ,[ef*] ... ,[ef])
       (make-begin `(,ef* ... ,ef))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(return-point ,label ,[Tail -> tail])
       `(return-point ,label ,tail)]
      [(mset! ,b ,o ,v)
       `(set! ,(make-index-opnd b o) ,v)]
      [(set! ,x (mref ,b ,o))
       `(set! ,x ,(make-index-opnd b o))]
      [(set! ,x (,binop ,y ,z))
       `(set! ,x (,binop ,y ,z))]
      [(set! ,x ,y) `(set! ,x ,y)]
      [,x (error who "invalid Effect ~s" x)]))
  (define (Pred pred)
    (match pred
      [(true) '(true)]
      [(false) '(false)]
      [(begin ,[Effect -> ef*] ... ,[pred])
       (make-begin `(,ef* ... ,pred))]
      [(if ,[pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(,relop ,x ,y) `(,relop ,x ,y)]
      [,x (error who "invalid Pred ~s" x)]))
  (define (Tail tail)
    (match tail
      [(begin ,[Effect -> ef*] ... ,[tail])
       (make-begin `(,ef* ... ,tail))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(,triv) `(,triv)]
      [,x (error who "invalid Tail ~s" x)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
       `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)]
      [,x (error who "invalid Tail ~s" x)])))
;---------------------------------------------------------------          

;---------------------------------------------------------------
; Pass:           
;   expose-basic-blocks
;
; Description: 
;   The idea of this pass is to create basic blocks for 
;   each "then", "else", and "join" parts, which results due
;   to branching operation of "if". These sequential blocks are
;   pushed to to the top as thunks. In the output language 
;   branching happens with conditional jumps based on the simpler 
;   form of (if (relop triv triv) (clab) (flab)). All these simple
;   "if" forms appear only in the tail position of the blocks.
;
;   Also in the case of non tail calls, the remaining portion 
;   after a return-point is pushed into a separate toplevel thunk.
;
; Input Language:  
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
;   Loc	    -->	reg | disp-opnd | index-opnd
;   Triv	-->	Loc | int | label 
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Tail)]*) Tail)
;   Tail	-->	(Triv)
;	         |	(if (relop Triv Triv) (,label) (,label))
;	         |	(begin Effect* Tail)
;   Effect  -->	(set! Loc Triv)
;	         |	(set! Loc (binop Triv Triv))
;   Loc     -->	reg | disp-opnd | index-opnd
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
;   Program	-->	(letrec ([label (lambda () Tail)]*) Tail)
;   Tail	-->	(Triv)
;	         |	(if (relop Triv Triv) (,label) (,label))
;	         |	(begin Effect* Tail)
;   Effect  -->	(set! Loc Triv)
;	         |	(set! Loc (binop Triv Triv))
;   Loc     -->	reg | disp-opnd | index-opnd
;   Triv	-->	Loc | int | label
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
; Compiler passes
;---------------------------------------------------------------
(compiler-passes '(
  verify-uil
  remove-complex-opera*
  flatten-set!
  impose-calling-conventions
  expose-allocation-pointer
  uncover-frame-conflict
  pre-assign-frame
  assign-new-frame
  (iterate
    finalize-frame-locations 
    select-instructions
    uncover-register-conflict
    assign-registers
    (break when everybody-home?)
    assign-frame)
  discard-call-live
  finalize-locations
  expose-frame-var
  expose-memory-operands
  expose-basic-blocks
  flatten-program
  generate-x86-64
))
;---------------------------------------------------------------