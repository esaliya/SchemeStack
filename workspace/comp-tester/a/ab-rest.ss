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
  (define remove-items
    (lambda (s l)
      (cond 
        [(or (null? s) (null? l)) s]
        [else (remove-items (remq (car l) s) (cdr l))])))
  (define (Expr ex)
    (match ex
      [(begin ,[ex* f**] ... ,[ex f*])
       (values (make-begin `(,ex* ... ,ex)) 
         (remove-common `(,f** ... ... ,f* ...)))]
      [(if ,[pred pf*] ,[conseq cf*] ,[alter af*])
       (values `(if ,pred ,conseq ,alter) 
         (remove-common `(,pf* ... ,cf* ... ,af* ...)))]
      [(let ([,uvar* ,[ex* f**]] ...) ,[ex f*])
       (let ([s (remove-items (remove-common `(,f** ... ... ,f* ...)) uvar*)])
         (values `(let ([,uvar* ,ex*] ...) ,ex) s))]
      [(letrec ([,uvar* (lambda (,fml** ...) ,[ex* f**])] ...) ,[ex f*])
       (let ([x** (map remove-items f** fml**)])
         (let ([s (remove-common (remove-items `(,x** ... ... ,f* ...) uvar*))])
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
        [(,prim ,[ex*] ...) (guard (memq prim primitives))
         `(,prim ,ex* ...)]
        ; Every procedure call will take its own closure pointer
        ; as the first argument
        [(,rator ,rator ,[ex*] ...)
         (if (and (uvar? rator) (memq rator f*))
             (let ([tmp (unique-name 'tmp)])
               `(let ([,tmp (procedure-ref ,cp (quote ,(set-idx rator f*)))])
                  ((procedure-code ,tmp) ,tmp ,ex* ...)))
             `((procedure-code ,rator) ,rator ,ex* ...))]
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

;---------------------------------------------------------------
;;; verify-a11-output accept a single value and verifies that the value
;;; is a valid program in the current source language.
;;;
;;; Grammar for verify-a11-output ,i.e. input to a10 passes (assignment 11):
;;;
;;;  Program --> (letrec ([<label> (lambda (<uvar>*) <Value>)]*) <Value>)
;;;  Value   --> <label>
;;;           |  <uvar>
;;;           |  (quote <Immediate>)
;;;           |  (if <Pred> <Value> <Value>)
;;;           |  (begin <Effect>* <Value>)
;;;           |  (let ([<uvar> <Value>]*) <Value>)
;;;           |  (<value-prim> <Value>*)
;;;           |  (<Value> <Value>*)
;;;  Pred    --> (true)
;;;           |  (false)
;;;           |  (if <Pred> <Pred> <Pred>)
;;;           |  (begin <Effect>* <Pred>)
;;;           |  (let ([<uvar> <Value>]*) <Pred>)
;;;           |  (<pred-prim> <Value>*)
;;;  Effect  --> (nop)
;;;           |  (if <Pred> <Effect> <Effect>)
;;;           |  (begin <Effect>* <Effect>)
;;;           |  (let ([<uvar> <Value>]*) <Effect>)
;;;           |  (<effect-prim> <Value>*)
;;;           |  (<Value> <Value>*)
;;;  Immediate -> <fixnum> | () | #t | #f
;;;
;;; Where uvar is symbol.n, n >= 0
;;;       label is symbol$n, n >= 0
;;;       fixnum is an exact integer
;;;       value-prims are void (zero arguments); car, cdr, vector-length,
;;;         make-vector (one argument); *, +, -, cons, vector-ref
;;;         (two arguments)
;;;       pred-prims are boolean?, fixnum?, null?, pair?, vector?
;;;         (one argument); <, <=, =, >=, >, eq? (two arguments)
;;;       effect-prims are set-car!, set-cdr! (two arguments);
;;;         vector-set! (three arguments)
;;;
;;; Each label bound by the letrec expression must have a unique suffix,
;;; and each uvar bound by a lambda or let expression must have a unique
;;; suffix, within the same Program.
;;;
;;; Machine constraints:
;;;   - each fixnum must be an exact integer n, -2^(k-1) <= n <= 2^(k-1)-1,
;;;     where k is the value of the helpers.ss variable fixnum-bits
;;;
;;; If the value is a valid program, verify-scheme returns the value
;;; unchanged; otherwise it signals an error.
;---------------------------------------------------------------
(define-who verify-a11-output
  (define value-prims
    '((* . 2) (+ . 2) (- . 2) (car . 1) (cdr . 1) (cons . 2)
       (make-vector . 1) (vector-length . 1) (vector-ref . 2)
       (make-procedure . 2) (procedure-ref . 2) (procedure-code . 1)
       (void . 0)))
  (define pred-prims
    '((< . 2) (<= . 2) (= . 2) (>= . 2) (> . 2) (boolean? . 1)
       (eq? . 2) (fixnum? . 1) (null? . 1) (pair? . 1)
       (vector? . 1) (procedure? . 1)))
  (define effect-prims '((set-car! . 2) (set-cdr! . 2) (vector-set! . 3) (procedure-set! . 3)))
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
  (define Program
    (lambda (x)
      (define all-uvar* '())
      (define Body
        (lambda (label* fml*)
          (define (Immediate imm)
            (cond
              [(memq imm '(#t #f ())) (values)]
              [(and (integer? imm) (exact? imm))
               (unless (fixnum-range? imm)
                 (error who "integer ~s is out of fixnum range" imm))
               (values)]
              [else (error who "invalid Immediate ~s" imm)]))
          (define Value
            (lambda (uvar*)
              (lambda (val)
                (match val
                  [,label (guard (label? label))
                   (if (memq label label*)
                       (values)
                       (error who "unbound label ~s" label))]
                  [,uvar (guard (uvar? uvar))
                   (if (memq uvar uvar*)
                       (values)
                       (error who "unbound uvar ~s" uvar))]
                  [(quote ,[Immediate ->]) (values)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(let ([,new-uvar* ,[]] ...) ,val)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Value (append new-uvar* uvar*)) val)]
                  [(,prim ,x* ...)
                   (guard (assq prim value-prims))
                   (unless (= (length x*) (cdr (assq prim value-prims)))
                     (error who "too many or few arguments ~s for ~s" (length x*) prim))
                   (for-each (Value uvar*) x*)
                   (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Value ~s" `(,x ,y ...))]
                  [(,[] ,[] ...) (values)]
                  [,val (error who "invalid Value ~s" val)]))))
          (define Effect
            (lambda (uvar*)
              (lambda (ef)
                (match ef
                  [(nop) (values)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[] ... ,[]) (values)]
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,ef)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Effect (append new-uvar* uvar*)) ef)]
                  [(,prim ,x* ...)
                   (guard (assq prim effect-prims))
                   (unless (= (length x*) (cdr (assq prim effect-prims)))
                     (error who "too many or few arguments ~s for ~s" (length x*) prim))
                   (for-each (Value uvar*) x*)
                   (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Effect ~s" `(,x ,y ...))]
                  [(,[(Value uvar*) ->] ,[(Value uvar*) ->] ...) (values)]
                  [,ef (error who "invalid Effect ~s" ef)]))))
          (define Pred
            (lambda (uvar*)
              (lambda (pr)
                (match pr
                  [(true) (values)]
                  [(false) (values)]
                  [(if ,[] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,pr)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Pred (append new-uvar* uvar*)) pr)]
                  [(,prim ,x* ...)
                   (guard (assq prim pred-prims))
                   (unless (= (length x*) (cdr (assq prim pred-prims)))
                     (error who "too many or few arguments ~s for ~s" (length x*) prim))
                   (for-each (Value uvar*) x*)
                   (values)]
                  [,pr (error who "invalid Pred ~s" pr)]))))
            (lambda (x) ((Value fml*) x))))
      (define Lambda
        (lambda (label*)
          (lambda (x)
            (match x
              [(lambda (,fml* ...) ,[(Body label* fml*) ->])
               (set! all-uvar* (append fml* all-uvar*))
               (values)]
              [,x (error who "invalid Lambda ~a" x)]))))
      (match x
        [(letrec ([,label* ,[(Lambda label*) ->]] ...) ,[(Body label* '()) ->])
         (verify-x-list label* label? 'label)
         (verify-x-list all-uvar* uvar? 'uvar)]
        [,x (error who "invalid Program ~s" x)])))
  (lambda (x) (Program x) x))
;---------------------------------------------------------------


;---------------------------------------------------------------
;;; Andy Keep, Kent Dybvig
;;; P423/P523
;;; Spring 2010

;;; verify-a10-output accept a single value and verifies that the value
;;; is a valid program in the current source language.
;;;
;;; Grammar for verify-a10-output ,i.e. input to a9 passes (assignment 11):
;;;
;;;  Program --> (letrec ([<label> (lambda (<uvar>*) <Tail>)]*) <Tail>)
;;;  Tail    --> <Triv>
;;;           |  (binop <Value> <Value>)
;;;           |  (alloc <Value>)
;;;           |  (<Value> <Value>*)
;;;           |  (if <Pred> <Tail> <Tail>)
;;;           |  (begin <Effect>* <Tail>)
;;;           |  (let ([<uvar> <Value>]*) <Tail>)
;;;  Pred    --> (true)
;;;           |  (false)
;;;           |  (<relop> <Value> <Value>)
;;;           |  (if <Pred> <Pred> <Pred>)
;;;           |  (begin <Effect>* <Pred>)
;;;           |  (let ([<uvar> <Value>]*) <Pred>)
;;;  Effect  --> (nop)
;;;           |  (mset! <Value> <Value> <Value>)
;;;           |  (<Value> <Value>*)
;;;           |  (if <Pred> <Effect> <Effect>)
;;;           |  (begin <Effect>* <Effect>)
;;;           |  (let ([<uvar> <Value>]*) <Effect>)
;;;  Value   --> <Triv>
;;;           |  (<binop> <Value> <Value>)
;;;           |  (alloc <Value>)
;;;           |  (<Value> <Value>*)
;;;           |  (if <Pred> <Value> <Value>)
;;;           |  (begin <Effect>* <Value>)
;;;           |  (let ([<uvar> <Value>]*) <Value>)
;;;  Triv    --> <uvar> | <integer> | <label>
;;;
;;; Where uvar is symbol.n, n >= 0
;;;       binop is mref +, -, *, logand, logor, or sra
;;;       relop is <, <=, =, >=, >
;;;       label is symbol$n, n >= 0
;;;
;;; Each label bound by the letrec expression must have a unique suffix,
;;; and each uvar bound by a lambda or let expression must have a unique
;;; suffix, within the same Program.
;;;
;;; Machine constraints:
;;;   - sra's second operand must be an exact integer k, 0 <= k <= 63
;;;   - each other integer must be a exact integer n, -2^63 <= n <= 2^63-1
;;;
;;; If the value is a valid program, verify-scheme returns the value
;;; unchanged; otherwise it signals an error.
;---------------------------------------------------------------
(define-who verify-a10-output
  (define binops '(mref + - * logand logor sra))
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
  (define Program
    (lambda (x)
      (define all-uvar* '())
      (define Body
        (lambda (label* fml*)
          (define Triv
            (lambda (uvar*)
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
            (lambda (uvar*)
              (lambda (val)
                (match val
                  [(let ([,new-uvar* ,[]] ...) ,val)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Value (append new-uvar* uvar*)) val)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(sra ,[] ,y)
                   (unless (uint6? y)
                     (error who "invalid sra operand ~s" y))
                   (values)]
                  [(,binop ,[] ,[])
                   (guard (memq binop binops))
                   (values)]
                  [(alloc ,[]) (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Value ~s" `(,x ,y ...))]
                  [(,[] ,[] ...) (values)]
                  [,[(Triv uvar*) ->] (values)]))))
          (define Effect
            (lambda (uvar*)
              (lambda (ef)
                (match ef
                  [(nop) (values)]
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,ef)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Effect (append new-uvar* uvar*)) ef)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[] ... ,[]) (values)]
                  [(mset! ,[(Value uvar*) ->] 
                          ,[(Value uvar*) ->] 
                          ,[(Value uvar*) ->])
                   (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Effect ~s" `(,x ,y ...))]
                  [(,[(Value uvar*) ->] ,[(Value uvar*) ->] ...) (values)]
                  [,ef (error who "invalid Effect ~s" ef)]))))
          (define Pred
            (lambda (uvar*)
              (lambda (pr)
                (match pr
                  [(true) (values)]
                  [(false) (values)]
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,pr)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Pred (append new-uvar* uvar*)) pr)]
                  [(if ,[] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(,relop ,[(Value uvar*) ->] ,[(Value uvar*) ->])
                   (guard (memq relop relops))
                   (values)]
                  [,pr (error who "invalid Pred ~s" pr)]))))
          (define Tail
            (lambda (uvar*)
              (lambda (tail)
                (match tail
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,tail)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Tail (append new-uvar* uvar*)) tail)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(sra ,[(Value uvar*) ->] ,y)
                   (unless (uint6? y)
                     (error who "invalid sra operand ~s" y))
                   (values)]
                  [(,binop ,[(Value uvar*) ->] ,[(Value uvar*) ->])
                   (guard (memq binop binops))
                   (values)]
                  [(alloc ,[]) (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Tail ~s" `(,x ,y ...))]
                  [(,[(Value uvar*) ->] ,[(Value uvar*) ->] ...) (values)]
                  [,[(Triv uvar*) ->] (values)]))))
            (lambda (tail) ((Tail fml*) tail))))
    (define Lambda
      (lambda (label*)
        (lambda (x)
          (match x
            [(lambda (,fml* ...) ,[(Body label* fml*) ->])
             (set! all-uvar* (append fml* all-uvar*))
             (values)]
            [,x (error who "invalid Lambda ~a" x)]))))
    (match x
      [(letrec ([,label* ,[(Lambda label*) ->]] ...) ,[(Body label* '()) ->])
       (verify-x-list label* label? 'label)
       (verify-x-list all-uvar* uvar? 'uvar)]
      [,x (error who "invalid Program ~s" x)])))
  (lambda (x) (Program x) x))
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
         (if (eq? label t)
             (set-cdr! (car junk*) target)
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
        ;; I will be able to handle the jumps to registers similarly by
        ;; using set-jumps! followed by (list-junks bnd* junk*) 
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


;---------------------------------------------------------------
;;; a12 - verifier
;;; Andy Keep, Kent Dybvig
;;; P423/P523
;;; Spring 2010

;;; verify-scheme accept a single value and verifies that the value
;;; is a valid program in the current source language.
;;;
;;; The grammar changes only slightly from Assignment 11 in that labels
;;; no longer appear in the source language.  Also, the set of variables
;;; visible within each lambda expression now includes those bound by
;;; let, letrec, and lambda expressions enclosing the lambda expression.
;;;
;;; Grammar for verify-scheme (assignment 12):
;;;
;;;  Program --> <Expr>
;;;  Expr   --> <uvar>
;;;          |  (quote <Immediate>)
;;;          |  (if <Expr> <Expr> <Expr>)
;;;          |  (begin <Expr>* <Expr>)
;;;          |  (let ([<uvar> <Expr>]*) <Expr>)
;;;          |  (letrec ([<uvar> (lambda (<uvar>*) <Expr>)]*) <Expr>)
;;;          |  (<primitive> <Expr>*)
;;;          |  (<Expr> <Expr>*)
;;;  Immediate -> <fixnum> | () | #t | #f
;;;
;;; Where uvar is symbol.n, n >= 0
;;;       fixnum is an exact integer
;;;       primitives are void (zero arguments); car, cdr, vector-length,
;;;         make-vector, boolean?, fixnum?, null?, pair?, procedure?,
;;;         vector? (one argument); *, +, -, cons, vector-ref, <, <=, =,
;;;         >=, >, eq?, set-car!, set-cdr! (two arguments); and vector-set!
;;;         (three arguments).
;;;
;;; Within the same Program, each uvar bound by a lambda, let, or letrec
;;; expression must have a unique suffix.
;;;
;;; Machine constraints:
;;;   - each fixnum must be an exact integer n, -2^(k-1) <= n <= 2^(k-1)-1,
;;;     where k is the value of the helpers.ss variable fixnum-bits
;;;
;;; If the value is a valid program, verify-scheme returns the value
;;; unchanged; otherwise it signals an error.

(define-who verify-scheme
  (define primitives
    '((+ . 2) (- . 2) (* . 2) (<= . 2) (< . 2) (= . 2)
      (>= . 2) (> . 2) (boolean? . 1) (car . 1) (cdr . 1)
      (cons . 2) (eq? . 2) (fixnum? . 1) (make-vector . 1)
      (null? . 1) (pair? . 1) (procedure? . 1) (set-car! . 2)
      (set-cdr! . 2) (vector? . 1) (vector-length . 1)
      (vector-ref . 2) (vector-set! . 3) (void . 0)))
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
  (define Program
    (lambda (x)
      (define all-uvar* '())
      (define Expr
        (lambda (uvar*)
          (lambda (x)
            (match x
              [,uvar (guard (uvar? uvar))
               (if (memq uvar uvar*)
                   (values)
                   (error who "unbound uvar ~s" uvar))]
              [(quote ,[Immediate ->]) (values)]
              [(if ,[] ,[] ,[]) (values)]
              [(begin ,[] ... ,[]) (values)]
              [(let ([,new-uvar* ,[]] ...) ,x)
               (set! all-uvar* (append new-uvar* all-uvar*))
               ((Expr (append new-uvar* uvar*)) x)]
              [(letrec ([,new-uvar* (lambda (,fml** ...) ,x*)] ...) ,x)
               (set! all-uvar* (append new-uvar* all-uvar*))
               (let ([uvar* (append new-uvar* uvar*)])
                 (for-each
                   (lambda (fml* x)
                     (set! all-uvar* (append fml* all-uvar*))
                     ((Expr (append fml* uvar*)) x))
                   fml**
                   x*)
                 ((Expr uvar*) x))]
              [(,prim ,x* ...)
               (guard (assq prim primitives))
               (unless (= (length x*) (cdr (assq prim primitives)))
                 (error who "too many or few arguments ~s for ~s" (length x*) prim))
               (for-each (Expr uvar*) x*)
               (values)]
              [(,x ,y ...)
               (guard (and (symbol? x) (not (uvar? x))))
               (error who "invalid Expr ~s" `(,x ,y ...))]
              [(,[] ,[] ...) (values)]
              [,x (error who "invalid Expr ~s" x)]))))
      (define (Immediate imm)
        (cond
          [(memq imm '(#t #f ())) (values)]
          [(and (integer? imm) (exact? imm))
           (unless (fixnum-range? imm)
             (error who "integer ~s is out of fixnum range" imm))
           (values)]
          [else (error who "invalid Immediate ~s" imm)]))
      ((Expr '()) x)
      (verify-x-list all-uvar* uvar? 'uvar)))
  (lambda (x) (Program x) x))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   uncover-locals
;
; Description: 
;   This pass will records all the variables 
;   bound by let expressions inside locals form
;
; Input Language:  
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
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
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
(define-who uncover-locals
  (define (binop? op)
    (memq op '(mref + - * logand logor sra)))
  (define (relop? op)
    (memq op '(< > <= >= =)))
  (define (Triv? t)
    (or (label? t) (uvar? t) (and (integer? t) (exact? t))))
  (define (Value val)
    (match val
      [(begin ,[Effect -> ef* eflocal**] ... ,[val vallocal*])
       (values (make-begin `(,ef* ... ,val)) `(,eflocal** ... ... ,vallocal* ...))]
      [(if ,[Pred -> pred predlocal*] ,[conseq conseqlocal*] ,[alter alterlocal*])
       (values `(if ,pred ,conseq ,alter) `(,predlocal* ... ,conseqlocal* ... ,alterlocal* ...))]
      [(alloc ,[val vallocal*]) (values `(alloc ,val) vallocal*)]
      [(let ([,uvar* ,[Value -> val* vallocal**]] ...) ,[val vallocal*])
       (values `(let ([,uvar* ,val*] ...) ,val) `(,uvar* ... ,vallocal** ... ... ,vallocal* ...))]
      [(,binop ,[x xlocal*] ,[y ylocal*]) (guard (binop? binop))
       (values `(,binop ,x ,y) `(,xlocal* ... ,ylocal* ...))]
      [(,[rator ratorlocal*] ,[rand* randlocal**] ...)
       (values `(,rator ,rand* ...) `(,ratorlocal* ... ,randlocal** ... ...))]
      [,triv (guard (Triv? triv)) (values triv '())]
      [,x (error who "invalid Value ~s" x)]))
  (define (Effect ef)
    (match ef
      [(nop) (values '(nop) '())]
      [(begin ,[ef* eflocal**] ... ,[ef eflocal*])
       (values (make-begin `(,ef* ... ,ef)) `(,eflocal** ... ... ,eflocal* ...))]
      [(if ,[Pred -> pred predlocal*] ,[conseq conseqlocal*] ,[alter alterlocal*])
       (values `(if ,pred ,conseq ,alter) `(,predlocal* ... ,conseqlocal* ... ,alterlocal* ...))]
      [(let ([,uvar* ,[Value -> val* vallocal**]] ...) ,[ef eflocal*])
       (values `(let ([,uvar* ,val*] ...) ,ef) `(,uvar* ... ,vallocal** ... ... ,eflocal* ...))]
      [(mset! ,[Value -> b blocal*] ,[Value -> o olocal*] ,[Value -> v vlocal*]) 
       (values `(mset! ,b ,o ,v) `(,blocal* ... ,olocal* ... ,vlocal* ...))]
      [(,[Value -> rator ratorlocal*] ,[Value -> rand* randlocal**] ...)
       (values `(,rator ,rand* ...) `(,ratorlocal* ... ,randlocal** ... ...))]
      [,x (error who "invalid Effect ~s" x)]))
  (define (Pred pred)
    (match pred
      [(true) (values '(true) '())]
      [(false) (values '(false) '())]
      [(begin ,[Effect -> ef* eflocal**] ... ,[pred predlocal*])
       (values (make-begin `(,ef* ... ,pred)) `(,eflocal** ... ... ,predlocal* ...))]
      [(if ,[pred predlocal*] ,[conseq conseqlocal*] ,[alter alterlocal*])
       (values `(if ,pred ,conseq ,alter) `(,predlocal* ... ,conseqlocal* ... ,alterlocal* ...))]
      [(let ([,uvar* ,[Value -> val* vallocal**]] ...) ,[pred predlocal*])
       (values `(let ([,uvar* ,val*] ...) ,pred) `(,uvar* ... ,vallocal** ... ... ,predlocal* ...))]
      [(,relop ,[Value -> x xlocal*] ,[Value -> y ylocal*]) (guard (relop? relop))
       (values `(,relop ,x ,y) `(,xlocal* ... ,ylocal* ...))]
      [,x (error who "invalid Pred ~s" x)])) 
  (define (Tail tail)
    (match tail
      [(begin ,[Effect -> ef* eflocal**] ... ,[t tlocal*])
       (values (make-begin `(,ef* ... ,t)) `(,eflocal** ... ... ,tlocal* ...))]
      [(if ,[Pred -> pred predlocal*] ,[conseq conseqlocal*] ,[alter alterlocal*])
       (values `(if ,pred ,conseq ,alter) `(,predlocal* ... ,conseqlocal* ... ,alterlocal* ...))]
      [(alloc ,[Value -> val vallocal*]) (values `(alloc ,val) vallocal*)]
      [(let ([,uvar* ,[Value -> val* vallocal**]] ...) ,[tail taillocal*])
       (values `(let ([,uvar* ,val*] ...) ,tail) `(,uvar* ... ,vallocal** ... ... ,taillocal* ...))]
      [(,binop ,[Value -> x xlocal*] ,[Value -> y ylocal*]) (guard (binop? binop))
       (values `(,binop ,x ,y) `(,xlocal* ... ,ylocal* ...))]
      [(,[Value -> rator ratorlocal*] ,[Value -> rand* randlocal**] ...)
       (values `(,rator ,rand* ...) `(,ratorlocal* ... ,randlocal** ... ...))]
      [,triv (guard (Triv? triv)) (values triv '())]
      [,x (error who "invalid Tail ~s" x)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,[Tail -> tail* local**])] ...) 
         ,[Tail -> tail local*])
       `(letrec ([,label* (lambda (,fml** ...) (locals (,local** ...) ,tail*))] ...)
          (locals (,local* ...) ,tail))])))
;---------------------------------------------------------------

;---------------------------------------------------------------
; Pass:           
;   remove-let
;
; Description: 
;   This pass will remove let expressions with a set of set!
;   to perform the variable bindings. The body of the let
;   expression is recursively transformed and placed following
;   the set! sequence.
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body	-->	(locals (uvar*) Tail)
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
;
; Output Language: 
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
;---------------------------------------------------------------
(define-who remove-let
  (define (binop? op)
    (memq op '(mref + - * logand logor sra)))
  (define (relop? op)
    (memq op '(< > <= >= =)))
  (define (Triv? t)
    (or (label? t) (uvar? t) (and (integer? t) (exact? t))))
  (define (Value val)
    (match val
      [(begin ,[Effect -> ef*] ... ,[val])
       (make-begin `(,ef* ... ,val))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(alloc ,[val]) `(alloc ,val)]
      [(let ([,uvar* ,[Value -> val*]] ...) ,[val])
       (make-begin
         `((set! ,uvar* ,val*) ... ,val))]
      [(,binop ,[x] ,[y]) (guard (binop? binop)) `(,binop ,x ,y)]
      [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
      [,triv (guard (Triv? triv)) triv]
      [,x (error who "invalid Value ~s" x)]))
  (define (Effect ef)
    (match ef
      [(nop) '(nop)]
      [(begin ,[ef*] ... ,[ef])
       (make-begin `(,ef* ... ,ef))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(let ([,uvar* ,[Value -> val*]] ...) ,[ef])
       (make-begin
         `((set! ,uvar* ,val*) ... ,ef))]
      [(mset! ,[Value -> b] ,[Value -> o] ,[Value -> v]) 
       `(mset! ,b ,o ,v)]
      [(,[Value -> rator] ,[Value -> rand*] ...)
       `(,rator ,rand* ...)]
      [,x (error who "invalid Effect ~s" x)]))
  (define (Pred pred)
    (match pred
      [(true) '(true)]
      [(false)'(false)]
      [(begin ,[Effect -> ef*] ... ,[pred])
       (make-begin `(,ef* ... ,pred))]
      [(if ,[pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(let ([,uvar* ,[Value -> val*]] ...) ,[pred])
       (make-begin
         `((set! ,uvar* ,val*) ... ,pred))]
      [(,relop ,[Value -> x] ,[Value -> y]) (guard (relop? relop))
       `(,relop ,x ,y)]
      [,x (error who "invalid Pred ~s" x)]))
  (define (Tail tail)
    (match tail
      [(begin ,[Effect -> ef*] ... ,[tail])
       (make-begin `(,ef* ... ,tail))]
      [(if ,[Pred -> pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(alloc ,[Value -> val]) `(alloc ,val)]
      [(let ([,uvar* ,[Value -> val*]] ...) ,[tail])
       (make-begin
         `((set! ,uvar* ,val*) ... ,tail))]
      [(,binop ,[Value -> x] ,[Value -> y]) (guard (binop? binop))
       `(,binop ,x ,y)]
      [(,[Value -> rator] ,[Value -> rand*] ...)
       `(,rator ,rand* ...)]
      [,triv (guard (Triv? triv)) triv]
      [,x (error who "invalid Tail ~s" x)]))
  (define (Body body)
    (match body
      [(locals (,local* ...) ,[Tail -> tail])
       `(locals (,local* ...) ,tail)]
      [,x (error who "invalid Body ~s" x)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda (,fml** ...) ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------