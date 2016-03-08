; Saliya Ekanayake
; sekanaya
; Assignment 6

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
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;  Value	-->	Triv
;	         |	(binop Value Value)
;	         |	(if Pred Value Value)
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
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;  Value	-->	Triv
;			 |	(binop Triv Triv)
;			 |	(if Pred Value Value)
;			 |	(begin Effect* Value)
;   Triv	-->	uvar | int | label
;---------------------------------------------------------------
(define-who remove-complex-opera*
  (define Body
    (lambda (body)
      (define newlocal* '())
      (define gen-newlocal
        (lambda ()
          (set! newlocal* (cons (unique-name 't) newlocal*))
          (car newlocal*)))
      (define select-complex
        (lambda (val*)
          (filter (lambda (val) (not (or (triv? val) (op? val)))) val*)))
      (define handle-complex
        (lambda (x)
          (match x
            [,triv (guard (triv? triv)) triv]
            [(if ,[Pred -> pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
            [(begin ,[Effect -> ef*] ... ,[val]) (make-begin `(,ef* ... ,val))]
            [(,val ,val* ...)
             (let ([complex* (select-complex `(,val ,val* ...))])
               (if (null? complex*)
                   `(,val ,val* ...)
                   (let ([complex-home* (map (lambda (complex) `(,complex . ,(gen-newlocal))) complex*)])
                     (make-begin
                       (let ([call (map (lambda (val)
                                          (if (or (triv? val) (op? val))
                                              val
                                              (cdr (assq val complex-home*))))
                                        `(,val ,val* ...))]
                             [assign* (map (lambda (complex)
                                             `(set! ,(cdr (assq complex complex-home*)) ,(handle-complex complex)))
                                           complex*)])
                         `(,assign* ... ,call))))))])))
      (define Value
        (lambda (val)
          (match val
            [,triv (guard (triv? triv)) triv]
            [(if ,[Pred -> pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
            [(begin ,[Effect -> ef*] ... ,[val]) (make-begin `(,ef* ... ,val))]
            [(,binop ,x ,y) (guard (binop? binop)) (handle-complex `(,binop ,x ,y))]
            [,x (error who "invalid Valu ~s" x)])))     
      (define Pred
        (lambda (pred)
          (match pred
            [(true) '(true)]
            [(false) '(false)]
            [(begin ,[Effect -> ef*] ... ,[pred]) (make-begin `(,ef* ... ,pred))]
            [(if ,[pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
            [(,relop ,val1 ,val2) (handle-complex `(,relop ,val1 ,val2))]
            [,x (error who "invalid Pred ~s" x)])))
      (define Effect
        (lambda (ef)
          (match ef
            [(nop) '(nop)]
            [(begin ,[ef*] ...) (make-begin ef*)]
            [(if ,[Pred -> pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
            [(set! ,uvar ,[handle-complex -> val]) `(set! ,uvar ,val)]
            [,x (error who "invalid Effect ~s" x)])))
      (define Tail
        (lambda (tail)
          (match tail
            [(begin ,[Effect -> ef*] ... ,[tail]) (make-begin `(,ef* ... ,tail))]
            [(if ,[Pred -> pred] ,[conseq] ,[alter]) `(if ,pred ,conseq ,alter)]
            [(,binop ,val1 ,val2) (guard (binop? binop)) (handle-complex `(,binop ,val1 ,val2))]
            [(,val ,val* ...) (handle-complex `(,val ,val* ...))]
            [,triv (guard (triv? triv)) triv]
            [,x (error who "invalid Tail ~s" x)])))
      (match body
        [(locals (,local* ...) ,[Tail -> tail])
         `(locals (,local* ... ,newlocal* ...) ,tail)]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,param** ...) ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda (,param** ...) ,body*)] ...) ,body)]
      [,x (error who "invalid Body ~s" x)])))
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
        [(,binop ,triv1 ,triv2) `(set! ,uvar (,binop ,triv1 ,triv2))]
        [,triv (guard (triv? triv)) `(set! ,uvar ,triv)]
        [,x (error who "invalid Value ~s" x)])))
  (define Effect
    (lambda (ef)
      (match ef
        [(nop) `(nop)]
        [(begin ,[ef*] ...) (make-begin ef*)]
        [(if ,[Pred -> pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(set! ,uvar ,val) (handle-set! uvar val)])))
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
; Input Language:  
;   Same as the output of flatten-set! pass.
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
;   Tail	-->	(Triv Loc*)
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
;			 |	(if Pred Effect Effect)
;			 |	(begin Effect* Effect)
;Loc	    -->	reg | fvar
;Var	    -->	uvar | Loc
;Triv	    -->	Var | int | label
;---------------------------------------------------------------
(define-who impose-calling-conventions
  (define preglen (lambda () (length parameter-registers)))
  (define Tail
    (lambda (rp)
      (lambda (tail)
        (match tail
          [(begin ,ef* ... ,[tail])
           (make-begin `(,ef* ... ,tail))]
          [(if ,pred ,[conseq] ,[alter])
           `(if ,pred ,conseq ,alter)]
          [(,binop ,triv1 ,triv2) (guard (binop? binop))
           (make-begin `((set! ,return-value-register (,binop ,triv1 ,triv2))
                         (,rp ,frame-pointer-register ,return-value-register)))]
          [(,triv ,triv* ...)
           (let ([call `(,triv ,frame-pointer-register, return-address-register)])
             (make-begin
               (let gen ([triv* triv*]
                         [count 0]
                         [head* '()]
                         [tail* '()])
                 (if (null? triv*)
                     `(,head* ... ,tail* ... (set! ,return-address-register ,rp) ,call)
                     (gen (cdr  triv*) (add1 count)
                          (if (< count (preglen))
                              head*
                              (let ([loc (index->frame-var (- count (preglen)))])
                                (set-cdr! call (append (cdr call) `(,loc)))
                                `(,head* ... (set! ,loc ,(car triv*)))))
                          (if (< count (preglen))
                              (let ([loc (list-ref parameter-registers count)])
                                (set-cdr! call (append (cdr call) `(,loc)))
                                `(,tail* ... (set! ,loc ,(car triv*))))
                              tail*))))))]
          [,triv (guard triv? triv)
           (make-begin `((set! ,return-value-register ,triv)
                         (,rp ,frame-pointer-register ,return-value-register)))]
          [,x (error who "invalid Tail ~s" x)]))))
  (define Body
    (lambda (body param*)
      (match body
        [(locals (,local* ...) ,tail)
         (let ([rp (unique-name 'rp)])
           `(locals (,local* ... ,rp ,param* ...)
              ,(make-begin 
                 `((set! ,rp ,return-address-register)
                   ,(if (not (null? param*))
                        (let gen ([param* param*] [count 0] [bnd* '()])
                          (if (null? param*)
                              bnd*
                              (gen (cdr param*)
                                   (add1 count)
                                   `((set! ,(car param*) 
                                           ,(if (< count (preglen))
                                                (list-ref parameter-registers count)
                                                (index->frame-var (- count (preglen))))) ,bnd* ...))))
                        '()) ...
                   ,((Tail rp) tail)))))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,param** ...) ,body*)] ...) ,body)
       `(letrec ([,label* (lambda () ,(map Body body* param**))] ...) ,(Body body '()))]
      [,x (error who "invalid Body ~s" x)])))
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
  (define Triv
    (lambda (triv)
      (if (frame-var? triv)
          (make-disp-opnd frame-pointer-register (ash (frame-var->index triv) word-shift))
          triv)))
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[pred] ,[pred1] ,[pred2])
         `(if ,pred ,pred1 ,pred2)]
        [(begin ,[Effect -> ef*] ... ,[pred])
         (make-begin `(,ef* ... ,pred))]
        [(true) '(true)]
        [(false) '(false)]
        [(,relop ,[Triv -> x] ,[Triv -> y])
         `(,relop ,x ,y)]
        [,x (error who "invalid Pred ~s" x)])))
  (define Effect
    (lambda (ef)
      (match ef
        [(set! ,[Triv -> x] (,binop ,[Triv -> x] ,[Triv -> y]))
         `(set! ,x (,binop ,x ,y))]
        [(set! ,[Triv -> x] ,[Triv -> y])
         `(set! ,x ,y)]
        [(if ,[Pred -> pred] ,[ef1] , [ef2])
         `(if ,pred ,ef1 ,ef2)]
        [(begin ,[ef*] ... ,[ef])
         (make-begin `(,ef* ... ,ef))]
        [(nop) '(nop)])))
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[tail])
         (make-begin `(,ef* ... ,tail))]
        [(if ,[Pred -> pred] ,[tail1] ,[tail2])
         `(if ,pred ,tail1 ,tail2)]
        [(,[Triv -> triv]) `(,triv)]
        [,x (error who "invalid Tail ~s" x)])))
  (lambda (s)
    (match s
      [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
       `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)]
      [,x (error who "invalid Program ~s" x)])))
;--------------------------------------------------------------- 


