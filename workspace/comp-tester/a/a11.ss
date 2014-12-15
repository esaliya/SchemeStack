; Saliya Ekanayake
; sekanaya
; Assignment 11

;---------------------------------------------------------------
; Pass:           
;   lift-letrec
;
; Description: 
;   This pass lifts all letrec expression to one top level
;   letrec. The modified body (i.e. the result of recurring
;   body through the pass) is placed in place of the original
;   body of letrec. 
;
; Input Language:  
;   Program	  --> Expr
;   Expr      --> label
;	           |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([label (lambda (uvar*) Expr)]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length,
;     vector-ref, void, <, <=, =, >=, >, boolean?, eq?, 
;     fixnum?, null?, pair?, vector?m set-car!, set-cdr!, vector-set!
;
; Output Language: 
;   Program	  --> (letrec ([label (lambda (uvar*) Expr)]*) Expr)
;   Expr      --> label
;	           |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length,
;     vector-ref, void, <, <=, =, >=, >, boolean?, eq?, 
;     fixnum?, null?, pair?, vector?m set-car!, set-cdr!, vector-set!
;---------------------------------------------------------------
(define-who lift-letrec
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector?
                  set-car! set-cdr! vector-set!))
  (define (Expr expr)
    (match expr
      [(begin ,[e* b**] ... ,[body bb*])
       (values (make-begin `(,e* ... ,body))
         `(,b** ... ... ,bb* ...))]
      [(if ,[t tbnd*] ,[c cbnd*] ,[a abnd*])
       (values `(if ,t ,c ,a) `(,tbnd* ... ,cbnd* ... ,abnd* ...))]
      [(quote ,imm) (values `(quote ,imm) '())]
      [(let ([,uvar* ,[e* b**]] ...) ,[body bb*])
       (values `(let ([,uvar* ,e*] ...) ,body) 
         `(,b** ... ... ,bb* ...))]
      [(letrec ([,label* (lambda (,fml** ...) ,[e* b**])] ...) ,[body bb*])
       (values body 
         `([,label* (lambda (,fml** ...) ,e*)] ... ,b** ... ... ,bb* ...))]
      [,label (guard (label? label)) (values label '())]
      [,uvar (guard (uvar? uvar)) (values uvar '())]
      [(,prim ,[e* b**] ...) (guard (memq prim primitives))
       (values `(,prim ,e* ...) `(,b** ... ...))]
      [(,[rator ratorb*] ,[rand* randb**] ...)
       (values `(,rator ,rand* ...) `(,ratorb* ... ,randb** ... ...))]
      [,x (error who "invalid Expr ~s" x)]))
  (lambda (x)
    (match x
      [,[Expr -> e b*] `(letrec (,b* ...) ,e)])))

(define (make-nopless-begin x*)
  (let ([x* (remove '(nop) x*)])
    (if (null? x*)
        '(nop)
        (make-begin x*))))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   normalize-context
;
; Description: 
;   Identifies the context of each expression and rewrites
;   program to adhere to the output language. Along with 
;   this partitioning of expressions into relevant context,
;   it partitions the primitive operations into proper contexts.
;
; Input Language:  
;   Program	  --> (letrec ([label (lambda (uvar*) Expr)]*) Expr)
;   Expr      --> label
;	           |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length,
;     vector-ref, void, <, <=, =, >=, >, boolean?, eq?, 
;     fixnum?, null?, pair?, vector?m set-car!, set-cdr!, vector-set!
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Value)]*) Value)
;   Value	-->	label
;            |	uvar
;            |	(quote Immediate)
;            |	(if Pred Value Value)
;            |	(begin Effect* Value)
;            |	(let ([uvar Value]*) Value)
;            |	(value-prim Value*)
;            |	(Value Value*)
;   Pred	-->	(true)
;            |	(false)
;            |	(if Pred Pred Pred)
;            |	(begin Effect* Pred)
;            |	(let ([uvar Value]*) Pred)
;            |	(pred-prim Value*)
;   Effect	-->	(nop)
;            |	(if Pred Effect Effect)
;            |	(begin Effect* Effect)
;            |	(let ([uvar Value]*) Effect)
;            |	(effect-prim Value*)
;            |	(Value Value*)
;   Immediate	-->	fixnum | () | #t | #f
;
;   value-prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length,
;     vector-ref, void
;
;   pred-prim:
;     <, <=, =, >=, >, boolean?, eq?, fixnum?, null?, pair?, vector?
;
;   effect-prim:
;     set-car!, set-cdr!, vector-set!
;
;---------------------------------------------------------------
(define-who normalize-context
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector?
                  set-car! set-cdr! vector-set!))
  (define value-prim '(+ - * car cdr cons make-vector vector-length vector-ref void))
  (define pred-prim '(< <= = >= > boolean? eq? fixnum? null? pair? vector?))
  (define effect-prim '(set-car! set-cdr! vector-set!))
  
  (define (Effect ef)
    (match ef
      [(begin ,[ef*] ... ,[ef])
       (make-nopless-begin `(,ef* ... ,ef))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(,prim ,rand* ...) (guard (memq prim primitives)) 
       (cond
         [(memq prim value-prim) 
          (make-nopless-begin (map Effect rand*))] 
         [(memq prim pred-prim) 
          (make-nopless-begin (map Effect rand*))]
         [(memq prim effect-prim) 
          `(,prim ,(map Value rand*) ...)])]
      [(quote ,imm) '(nop)]
      [(let ([,uvar* ,[Value -> val*]] ...) ,[ef])
       `(let ([,uvar* ,val*] ...) ,ef)]
      [(,[Value -> rator] ,[Value -> rand*] ...)
       `(,rator ,rand* ...)]
      [,x (guard (or (label? x) (uvar? x))) '(nop)]
      [,x (error who "invalid Effect ~s" x)]))
  (define (Pred pred)
    (match pred
      [(begin ,[Effect -> ef*] ... ,[pred])
       (make-nopless-begin `(,ef* ... ,pred))]
      [(if ,[pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(,prim ,[Value -> val*] ...) (guard (memq prim primitives)) 
       (cond
         [(memq prim value-prim) 
          `(if (eq? (,prim ,val* ...) (quote #f)) (false) (true))] 
         [(memq prim pred-prim) 
          `(,prim ,val* ...)]
         [(memq prim effect-prim) 
          (make-nopless-begin `((,prim ,val* ...) (true)))])]
      [(quote ,imm) (if (eq? imm #f) '(false) '(true))]
      [(let ([,uvar* ,[Value -> val*]] ...) ,[pred])
       `(let ([,uvar* ,val*] ...) ,pred)]
      [(,[Value -> rator] ,[Value -> rand*] ...)
       `(if (eq? (,rator ,rand* ...) (quote #f)) (false) (true))]
      [,label (guard (label? label)) (true)]      
      [,uvar (guard (uvar? uvar))
       `(if (eq? ,uvar (quote #f)) (false) (true))]
      [,x (error who "invalid Pred ~s" x)]))
  (define (Value val)
    (match val
      [(begin ,[Effect -> ef*] ... ,[val])
       (make-nopless-begin `(,ef* ... ,val))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(,prim ,[val*] ...) (guard (memq prim primitives)) 
       (cond
         [(memq prim value-prim) `(,prim ,val* ...)]
         [(memq prim pred-prim) 
          `(if (,prim ,val* ...) (quote #t) (quote #f))]
         [(memq prim effect-prim) 
          (make-nopless-begin `((,prim ,val* ...) (void)))])]
      [(quote ,imm) `(quote ,imm)]
      [(let ([,uvar* ,[val*]] ...) ,[val])
       `(let ([,uvar* ,val*] ...) ,val)]
      [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
      [,label (guard (label? label)) label]
      [,uvar (guard (uvar? uvar)) uvar]
      [,x (error who "invalid Value ~s" x)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,[Value -> val*])] ...)
         ,[Value -> val])
       `(letrec ([,label* (lambda (,fml** ...) ,val*)] ...) ,val)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   optimize-jumps
;
; Description: 
;   Relies on the output of expose-basic-block pass. This is
;   an optimization pass, which will remove letrec bindings
;   that are pure jumps. 
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
;   Program	-->	(letrec ([label (lambda () Tail)]*) Tail)
;   Tail	-->	(Triv)
;	         |	(if (relop Triv Triv) (,label) (,label))
;	         |	(begin Effect* Tail)
;   Effect  -->	(set! Loc Triv)
;	         |	(set! Loc (binop Triv Triv))
;   Loc     -->	reg | disp-opnd | index-opnd
;   Triv	-->	Loc | int | label
;---------------------------------------------------------------
(define-who optimize-jumps
  (define set-jumps!
    (lambda (junk* label target)
      (match junk*
        [() (void)]
        [([,l . ,t] ,j* ...)
         (begin
           (if (eq? label t) (set-cdr! (car junk*) target))
           (set-jumps! j* label target))])))
  (define list-junks
    (lambda (bnd* junk*)
      (match bnd*
        [() junk*]
        [([,l . (,t)] ,bnd* ...)
         (if (label? t)
             (let ([kv (assq t junk*)])
               (if kv
                   (if (eq? l (cdr kv))
                       (list-junks bnd* junk*)
                       (list-junks bnd* (cons `(,l . ,(cdr kv)) junk*)))
                   (begin (set-jumps! junk* l t)
                     (list-junks bnd* (cons `(,l . ,t) junk*)))))
             (list-junks bnd* junk*))]
        [([,l . ,t] ,bnd* ...) (list-junks bnd* junk*)])))
  (define (Triv junk*)
    (lambda (t)
      (match t
        [,l (guard (label? l)) 
         (let ([kv (assq l junk*)])
           (if kv (cdr kv) l))]
        [,x (guard (or (register? x) (disp-opnd? x)
                       (index-opnd? x) (integer? x))) x]
        [,x (error who "invalid Triv ~s" x)])))
  (define (Effect junk*)
    (lambda (ef)
      (match ef
        [(set! ,loc (,binop ,[(Triv junk*) -> x] ,[(Triv junk*) -> y]))
         `(set! ,loc (,binop ,x ,y))]
        [(set! ,loc ,[(Triv junk*) -> t])
         `(set! ,loc ,t)]
        [,x (error who "invalid Effect ~s" x)])))
  (define (Tail junk*)
    (lambda (tail)
      (match tail
        [(begin ,[(Effect junk*) -> ef*] ... ,[tail])
         (make-begin `(,ef* ... ,tail))]
        [(if (,relop ,[(Triv junk*) -> x] ,[(Triv junk*) -> y])
             ,[conseq] ,[alter])
         `(if (,relop ,x ,y) ,conseq ,alter)]
        [(,[(Triv junk*) -> t]) `(,t)]
        [,x (error who "invalid Tail ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
       (let ([bnd* `([,label* . ,tail*] ...)])
         (let ([junk* (list-junks bnd* '())])
           (let ([bnd* (filter (lambda (bnd) 
                                 (not (assq (car bnd) junk*))) bnd*)])
             `(letrec ([,(map car bnd*) 
                         (lambda () ,(map (lambda (bnd)
                                            ((Tail junk*) (cdr bnd)))
                                          bnd*))] ...)
                ,((Tail junk*) tail)))))])))  
;---------------------------------------------------------------