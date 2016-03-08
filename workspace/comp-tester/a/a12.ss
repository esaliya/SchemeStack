; Saliya Ekanayake
; sekanaya
; Assignment 12

;---------------------------------------------------------------
; Pass:           
;   uncover-free
;
; Description: 
;   Finds all the free variables for lambda expressions and
;   record them in the new form 'free' inside lambda.
;
; Input Language:  
;   Program	  --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar (lambda (uvar*) Expr)]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;
; Output Language: 
;   Program	  --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar (lambda (uvar*) (free (uvar*) Expr))]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;---------------------------------------------------------------
(define-who uncover-free
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  (define remove-common
    (lambda (s)
      (cond
        [(null? s) '()]
        [else (cons (car s) (remove-common (remq (car s) (cdr s))))])))
  
  (define (Expr ex)
    (match ex
      [(begin ,[ex* f**] ... ,[ex f*])
       (values (make-begin `(,ex* ... ,ex)) 
         (remove-common `(,f** ... ... ,f* ...)))]
      [(if ,[pred pf*] ,[conseq cf*] ,[alter af*])
       (values `(if ,pred ,conseq ,alter) 
         (remove-common `(,pf* ... ,cf* ... ,af* ...)))]
      [(let ([,uvar* ,[ex* f**]] ...) ,[ex f*])
       (let ([s (difference (remove-common `(,f** ... ... ,f* ...)) uvar*)])
         (values `(let ([,uvar* ,ex*] ...) ,ex) s))]
      [(letrec ([,uvar* (lambda (,fml** ...) ,[ex* f**])] ...) ,[ex f*])
       (let ([x** (map difference f** fml**)])
         (let ([s (remove-common (difference `(,x** ... ... ,f* ...) uvar*))])
           (values 
             `(letrec ([,uvar* (lambda (,fml** ...) 
                                 (free (,(map remove-common x**) ...) ,ex*))] ...)
                ,ex) s)))]
      [(quote ,imm) (values `(quote ,imm) '())]
      [(,prim ,[ex* f**] ...) (guard (memq prim primitives))
       (values `(,prim ,ex* ...) (remove-common `(,f** ... ...)))]
      [(,[rator f*] ,[rand* f**] ...)
       (values `(,rator ,rand* ...) (remove-common `(,f* ... ,f** ... ...)))]
      [,uvar (guard (uvar? uvar)) (values uvar `(,uvar))]
      [,x (error who "invalid Expr ~S" x)]))
  (lambda (x)
    (match x
      [,[Expr -> ex f*] 
        (if (null? f*) ex (error who "Unbound variables ~s" f*))])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   convert-closures
;
; Description: 
;   Creates two new forms, which are used by later passes to
;   to create actual closures for procedures. Each lambda 
;   function is added with a new closure pointer parameter
;   as the first parameter. The bind-free form inside lambda
;   captures the closure pointer and the set of free variables
;   in order. The order, though not specific, is maintained 
;   throught to make it possible for later passes to retrieve
;   the free variables by giving the index from the listed order.
;   
;   The closures form introduced for the body of letrec expressions
;   captures the assocation of the unique variable, which was bound
;   to the procedure in the source language, and the unique label
;   used to represent the particular procedure in later passes along
;   with its free variables.
;
; Input Language:  
;   Program	  --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar (lambda (uvar*) (free (uvar*) Expr))]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;
; Output Language: 
;   Program	  --> Expr
;   Expr      --> label
;              |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([label (lambda (uvar*) (bind-free (uvar*) Expr))]*)
;                   (closures ([uvar label uvar*]*) Expr))
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;---------------------------------------------------------------
(define-who convert-closures
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  (define (Expr ex)
    (match ex
      [(begin ,[ex*] ... ,[ex])
       (make-begin `(,ex* ... ,ex))]
      [(if ,[pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(let ([,uvar* ,[ex*]] ...) ,[ex])
       `(let ([,uvar* ,ex*] ...) ,ex)]
      [(letrec ([,uvar* (lambda (,fml** ...) (free (,f** ...) ,[ex*]))] ...) ,[ex])
       (let ([lb* (map unique-label uvar*)]
             [cp* (map (lambda (uvar) (unique-name 'cp)) uvar*)])
         `(letrec ([,lb* (lambda (,cp* ,fml** ...)
                           (bind-free (,cp* ,f** ...)
                             ,ex*))] ...)
            (closures ([,uvar* ,lb* ,f** ...] ...)
              ,ex)))]
      [(quote ,imm) `(quote ,imm)]
      [(,prim ,[ex*] ...) (guard (memq prim primitives))
       `(,prim ,ex* ...)]
      [(,[rator] ,[rand*] ...)
       (if (uvar? rator)
           `(,rator ,rator ,rand* ...)
           (let ([tmp (unique-name 'tmp)])
             `(let ([,tmp ,rator]) (,tmp ,tmp ,rand* ...))))]
      [,uvar (guard (uvar? uvar)) uvar]
      [,x (error who "invalid Expr ~s" x)]))
  (lambda (x)
    (match x
      [,[Expr -> ex] ex])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   introduce-procedure-primitives
;
; Description: 
;   This pass introduces the procedure primitives,
;   i.e. make-procedure, procedure-ref, procedure-code, and
;   procedure-set!, to handle creation and manipulation of
;   closures. Later passes are responsible for converting
;   these primitives into UIL constructs. 
;
; Input Language:  
;   Program	  --> Expr
;   Expr      --> label
;              |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([label (lambda (uvar*) (bind-free (uvar*) Expr))]*)
;                   (closures ([uvar label uvar*]*) Expr))
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;
; Output Language: 
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
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who introduce-procedure-primitives
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  ; Helper to get the index of an element from a set
  (define set-idx
    (lambda (x s)
      (- (length s) (length (memq x s)))))
  (define (Lambda lamb)
    (match lamb
      [(lambda (,cp ,uvar* ...) (bind-free (,cp ,f* ...) ,ex))
       (let ([ex ((Expr cp f*) ex)])
         `(lambda (,cp ,uvar* ...) ,ex))]
      ;; This is when cp is removed by an optimization pass
      ;; the bind-free will capture a dummy variable because
      ;; one condition to remove cp is to have no free variables
      ;; (the second is that the closure should be well-known (see C) 
      [(lambda (,uvar* ...) (bind-free (,dummy) ,ex))
       `(lambda (,uvar* ...) ,((Expr 'dummy.cp '()) ex))]
      [,x (error who "invalid Lambda ~s" x)]))
  (define (Expr cp f*)
    (lambda (ex)
      (match ex
        [(begin ,[ex*] ... ,[ex])
         (make-begin `(,ex* ... ,ex))]
        [(if ,[pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(quote ,imm) `(quote ,imm)]
        [(let ([,uvar* ,[ex*]] ...) ,[ex])
         `(let ([,uvar* ,ex*] ...) ,ex)]
        [(,prim ,ex* ...) (guard (memq prim primitives))
         `(,prim ,(map (Expr cp f*) ex*) ...)]
        ; We will handle closures form independently though it 
        ; occurs only inside letrec
        [(letrec ([,label* ,[Lambda -> lamb*]] ...) ,[closex])
         `(letrec ([,label* ,lamb*] ...) ,closex)]
        [(closures ([,[cp*] ,[lb*] ,[f**] ...] ...) ,[ex])
         (let ([bnd* (map (lambda (cp lb f*)
                            `(,cp (make-procedure ,lb (quote ,(length f*)))))
                          cp* lb* f**)]
               [pset (map
                      (lambda (cp f*)
                        (map
                         (lambda (fx)
                           `(procedure-set! ,cp (quote ,(set-idx fx f*)) ,fx)) f*))
                      cp* f**)])
           `(let ,bnd* ,(make-begin `(,pset ... ... ,ex))))]
        [,label (guard (label? label)) label]
        [,uvar (guard (uvar? uvar)) 
          (if (memq uvar f*)
              `(procedure-ref ,cp (quote ,(set-idx uvar f*)))
              uvar)]
        ;; Handle direct jumps separately. This is because an optimization pass
        ;; (see C) may remove the closure pointer, which appears as the first
        ;; rand, from some applications that are of direct form and when the 
        ;; particular cp refers to a well-known and empty closure. Handling this
        ;; separately makes it possible to tackle the unnecessary generation of
        ;; (procedure-ref cp idx) twice when rator is a free variable. This form
        ;; will never come across the particular situation, even if a cp is present
        ;; as the first rand or not, since rator is a label.
        [(,label ,[rand*] ...) (guard (label? label))
         `(,label ,rand* ...)]
        ;; Handling the former clause separately gurantees that irrespective 
        ;; of the presence of an optimization pass (see C), this will always
        ;; have a cp as the first argument. Also at this level it is guaranteed
        ;; that both rator and ratorcp are the same uvars thanks to convert-closures.
        ;; Any optimization done after convert-closures will get handled in the 
        ;; former clause.
        [(,rator ,rator ,[ex*] ...)
         (if (memq rator f*)
             (let ([tmp (unique-name 'tmp)])
               `(let ([,tmp (procedure-ref ,cp (quote ,(set-idx rator f*)))])
                  ((procedure-code ,tmp) ,tmp ,ex* ...)))
             `((procedure-code ,rator) ,rator ,ex* ...))] 
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (match x
      [,[(Expr 'dummy.cp '()) -> ex] ex])))
;---------------------------------------------------------------

       
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
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
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
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who lift-letrec
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref
                        make-procedure procedure-ref procedure-code void
                        < <= = >= > boolean? eq? procedure? fixnum? null? pair? vector?
                        set-car! set-cdr! vector-set! procedure-set!))
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
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
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
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void
;
;   pred-prim:
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;
;   effect-prim:
;     set-car!, set-cdr!, vector-set!, procedure-set!
;
;---------------------------------------------------------------
(define-who normalize-context
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref
                        make-procedure procedure-ref procedure-code void
                        < <= = >= > boolean? eq? procedure? fixnum? null? pair? vector?
                        set-car! set-cdr! vector-set! procedure-set!))
  (define value-prim '(+ - * car cdr cons make-vector vector-length vector-ref
                        make-procedure procedure-ref procedure-code void))
  (define pred-prim '(< <= = >= > boolean? eq? procedure? fixnum? null? pair? vector?))
  (define effect-prim '(set-car! set-cdr! vector-set! procedure-set!))
  
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
;   specify-representation
;
; Description: 
;   This pass encodes Scheme objects as integers in UIL.
;   The representation, ptr, is based on the low-tagging.
;   Immediate objects, i.e. fixnum, #t, #t, (), and void
;   primitive are tagged with three low order bit tags 
;   leaving the value (for fixnum) in the remaining 61 high
;   order bits. The rest other than fixnums use a common
;   three low order bit tag with a unique high order five
;   bit tag following that. 
;
;   Heap allocated objects are represented by a ptr with 
;   true-address + tag. The memory alignment in x64 system
;   naturally makes it all zero for low 3 bits for memory
;   addresses. This makes it possible to use the tagging
;   without distorting the effective true address bits.
;
;   This pass also transforms Scheme primitive operations 
;   to UIL operations. 
;
; Input Language:  
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
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void
;
;   pred-prim:
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;
;   effect-prim:
;     set-car!, set-cdr!, vector-set!, procedure-set!
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Tail)]*) Tail)
;   Tail	-->	Triv
;	         |	(alloc Value)
;	         |	(binop Value Value)
;	         |	(Value Value*)
;	         |	(if Pred Tail Tail)
;	         |	(begin Effect* Tail)
;            |  (let ([uvar Value]*) Tail)
;   Pred	-->	(true)
;	         |	(false)
;	         |	(relop Value Value)
;            |	(if Pred Pred Pred)
;	         |	(begin Effect* Pred)
;            |  (let ([uvar Value]*) Pred)
;  Effect	-->	(nop)
;	         |	(mset! Value Value Value)
;            |  (Value Value*)
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;            |  (let ([uvar Value]*) Effect)
;  Value	-->	Triv
;	         |	(alloc Value)
;	         |	(binop Value Value)
;            |  (Value Value*)
;	         |	(if Pred Value Value)
;	         |	(begin Effect* Value)
;            |  (let ([uvar Value]*) Value)
;   Triv	-->	uvar | int | label 
;---------------------------------------------------------------
(define-who specify-representation
  (define value-prim '(+ - * car cdr cons make-vector vector-length vector-ref
                        make-procedure procedure-ref procedure-code void))
  (define pred-prim '(< <= = >= > boolean? eq? procedure? fixnum? null? pair? vector?))
  (define effect-prim '(set-car! set-cdr! vector-set! procedure-set!))

  (define imm-op '(+ - * < <= = >= > void))
  (define non-imm-op '(car cdr cons make-vector vector-length vector-ref
                        make-procedure procedure-ref procedure-code
                        set-car! set-cdr! vector-set! procedure-set!))
  (define pred-op '(boolean? fixnum? null? pair? vector? procedure? eq?))
  
  (define (handle-primitive x)
    (match x
      [(,prim ,val* ...) 
       (let ([f (cond
                  [(memq prim imm-op) handle-imm-op]
                  [(memq prim non-imm-op) handle-non-imm-op]
                  [(memq prim pred-op) handle-pred-op])])
         (f `(,prim ,val* ...)))]))
  (define (handle-imm-op x)
    (match x
      [(void) $void]
      [(* ,x ,y) 
       (cond
         [(integer? x) `(* ,(sra x shift-fixnum) ,y)]
         [(integer? y) `(* ,x ,(sra y shift-fixnum))]
         [else `(* ,x (sra ,y ,shift-fixnum))])]
      [(,op ,val* ...) `(,op ,val* ...)]))
  (define (handle-non-imm-op x)
    (match x
      [(car ,e) `(mref ,e ,(- disp-car tag-pair))]
      [(cdr ,e) `(mref ,e ,(- disp-cdr tag-pair))]
      [(cons ,e1 ,e2) 
       (let ([tmp-car (unique-name 't)] 
             [tmp-cdr (unique-name 't)] 
             [tmp (unique-name 't)])
         `(let ([,tmp-car ,e1] [,tmp-cdr ,e2])
            (let ([,tmp (+ (alloc ,size-pair) ,tag-pair)])
              ,(make-begin
                 `((mset! ,tmp ,(- disp-car tag-pair) ,tmp-car)
                   (mset! ,tmp ,(- disp-cdr tag-pair) ,tmp-cdr)
                   ,tmp)))))]
      [(set-car! ,e1 ,e2)
       `(mset! ,e1 ,(- disp-car tag-pair) ,e2)]
      [(set-cdr! ,e1 ,e2)
       `(mset! ,e1 ,(- disp-cdr tag-pair) ,e2)]
      [(vector-ref ,e1 ,e2)
       (if (and (integer? e2) (exact? e2))
           `(mref ,e1 ,(+ (- disp-vector-data tag-vector) e2))
           `(mref ,e1 (+ ,(- disp-vector-data tag-vector) ,e2)))]
      [(vector-set! ,e1 ,e2 ,e3)
       (if (and (integer? e2) (exact? e2))
           `(mset! ,e1 ,(+ (- disp-vector-data tag-vector) e2) ,e3)
           `(mset! ,e1 (+ ,(- disp-vector-data tag-vector) ,e2) ,e3))]
      [(vector-length ,e)
       `(mref ,e ,(- disp-vector-length tag-vector))]
      [(make-vector ,e)
       (if (and (integer? e) (exact? e))
           (let ([tmp (unique-name 't)])
             `(let ([,tmp (+ (alloc ,(+ disp-vector-data e)) ,tag-vector)])
                ,(make-begin
                   `((mset! ,tmp ,(- disp-vector-length tag-vector) ,e)
                     ,tmp))))
           (let ([tmp1 (unique-name 't)] [tmp2 (unique-name 't)])
             `(let ([,tmp1 ,e])
                (let ([,tmp2 (+ (alloc (+ ,disp-vector-data ,tmp1)) ,tag-vector)])
                  ,(make-begin
                     `((mset! ,tmp2 ,(- disp-vector-length tag-vector) ,tmp1)
                       ,tmp2))))))]
      [(make-procedure ,lb ,n) (guard (and (integer? n) (exact? n)))
       (let ([tmp (unique-name 't)])
         `(let ([,tmp (+ (alloc ,(+ disp-procedure-data n)) ,tag-procedure)])
            ,(make-begin
              `((mset! ,tmp ,(- disp-procedure-code tag-procedure) ,lb)
                ,tmp))))]
      [(procedure-code ,e)
       `(mref ,e ,(- disp-procedure-code tag-procedure))]
      [(procedure-ref ,cp ,idx) (guard (and (integer? idx) (exact? idx)))
       `(mref ,cp ,(+ (- disp-procedure-data tag-procedure) idx))]
      [(procedure-set! ,e1 ,idx ,e2) (guard (and (integer? idx) (exact? idx)))
       `(mset! ,e1 ,(+ (- disp-procedure-data tag-procedure) idx) ,e2)]))
  (define (handle-pred-op x)
    (match x
      [(boolean? ,e) `(= (logand ,e ,mask-boolean) ,tag-boolean)]
      [(fixnum? ,e) `(= (logand ,e ,mask-fixnum) ,tag-fixnum)]
      [(pair? ,e) `(= (logand ,e ,mask-pair) ,tag-pair)]
      [(vector? ,e) `(= (logand ,e ,mask-vector) ,tag-vector)]
      [(procedure? ,e) `(= (logand ,e ,mask-procedure) ,tag-procedure)]
      [(null? ,e) `(= ,e ,$nil)]
      [(eq? ,e1 ,e2) `(= ,e1 ,e2)]))
  (define (Immediate imm)
    (match imm
      [#t $true]
      [#f $false]
      [() $nil]
      [,x (guard (and (integer? x) (exact? x) (fixnum-range? x)))
       (ash x shift-fixnum)]
      [,x (error who "invalid Immediate ~s" x)]))
  (define (Effect ef)
    (match ef
      [(nop) '(nop)]
      [(begin ,[ef*] ... ,[ef])
       (make-begin `(,ef* ... ,ef))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(let ([,uvar* ,[Value -> val*]] ...) ,[ef])
       `(let ([,uvar* ,val*] ...) ,ef)]
      [(,prim ,[Value -> val*] ...) (guard (memq prim effect-prim))
       (handle-primitive `(,prim ,val* ...))]
      [(,[Value -> rator] ,[Value -> rand*] ...)
       `(,rator ,rand* ...)]
      [,x (error who "invalid Effect ~s" x)]))     
  (define (Pred pred)
    (match pred
      [(true) '(true)]
      [(false) '(false)]
      [(begin ,[Effect -> ef*] ... ,[pred])
       (make-begin `(,ef* ... ,pred))]
      [(if ,[pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(let ([,uvar* ,[Value -> val*]] ...) ,[pred])
       `(let ([,uvar* ,val*] ...) ,pred)]
      [(,prim ,[Value -> val*] ...) (guard (memq prim pred-prim))
       (handle-primitive `(,prim ,val* ...))]
      [,x (error who "invalid Pred ~s" x)]))
  (define (Value val)
    (match val
      [(begin ,[Effect -> ef*] ... ,[val])
       (make-begin `(,ef* ... ,val))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(let ([,uvar* ,[val*]] ...) ,[val])
       `(let ([,uvar* ,val*] ...) ,val)]
      [(quote ,[Immediate -> imm]) imm]
      [(,prim ,[val*] ...) (guard (memq prim value-prim))
       (handle-primitive `(,prim ,val* ...))]
      [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
      [,label (guard (label? label)) label]
      [,uvar (guard (uvar? uvar)) uvar]
      [,x (error who "invalid Value ~s" x)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,[Value -> val*])] ...) ,[Value -> val])
       `(letrec ([,label* (lambda (,fml** ...) ,val*)] ...) ,val)]
      [,x (error who "invalid Program ~s" x)])))       
 ;---------------------------------------------------------------      
       
       
       
       
       
       
       
       
       
       
       
       
       
       




  