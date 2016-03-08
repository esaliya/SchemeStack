; Saliya Ekanayake
; sekanaya
; Assignment 13

;---------------------------------------------------------------
; Pass:           
;   optimize-direct-call
;
; Description: 
;   This pass introduces a let transfomation for an application
;   when the operator is an anonymous lambda. This is an 
;   optimization pass and does not change the input language.   
;   The transformation is as follows.
;
;   ((lambda (fml*) body) arg*) -> (let ([fml* arg*] ...) body)
;
; Input Language:  
;   Program   --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;	           |  (begin Expr* Expr)
;	           |  Lambda
;	           |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar Lambda]*) Expr)
;	           |  (prim Expr*)
;	           |  (Expr Expr*)
;   Lambda    --> (lambda (uvar*) Expr)
;   Immediate --> fixnum | () | #t | #f
;
; Output Language: 
;   Program   --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;	           |  (begin Expr* Expr)
;	           |  Lambda
;	           |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar Lambda]*) Expr)
;	           |  (prim Expr*)
;	           |  (Expr Expr*)
;   Lambda    --> (lambda (uvar*) Expr)
;   Immediate --> fixnum | () | #t | #f
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who optimize-direct-call
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  (define (lambda? lamb)
    (match lamb
      [(lambda (,fml* ...) ,ex) #t]
      [,x #f]))
  (define (Lambda lamb)
    (match lamb
      [(lambda (,fml* ...) ,[Expr -> ex])
       `(lambda (,fml* ...) ,ex)]
      [,x (error who "invalid Lambda ~s" x)]))
  (define (Expr ex)
    (match ex
      [(begin ,[ex*] ... ,[ex])
       (make-begin `(,ex* ... ,ex))]
      [(if ,[pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(quote ,imm) `(quote ,imm)]
      [(let ([,uvar* ,[ex*]] ...) ,[ex])
       `(let ([,uvar* ,ex*] ...) ,ex)]
      [(letrec ([,uvar* ,[Lambda -> lamb*]] ...) ,[ex])
       `(letrec ([,uvar* ,lamb*] ...) ,ex)]
      [(,prim ,ex* ...) (guard (memq prim primitives))  
       `(,prim ,(map Expr ex*) ...)]
      [,uvar (guard (uvar? uvar)) uvar]
      [,lamb (guard (lambda? lamb)) (Lambda lamb)]
      ; Special case the direct call
      [((lambda (,fml* ...) ,[ex]) ,[ex*] ...)
       (if (eq? (length fml*) (length ex*))
           `(let ([,fml* ,ex*] ...) ,ex)
           (error who "incorrect number of arguments to procedure"))]
      [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
      [,x (error who "invalid Expr ~s" x)]))
  (lambda (x)
    (match x
      [,[Expr -> ex] ex])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   remove-anonymous-lambda
;
; Description: 
;   This pass replaces anonymous lambda expressions with a 
;   letrec binding which creates a unique variable for the
;   for the lambda binding and return it in the body of   
;   letrec expression.
;
; Input Language:  
;   Program   --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;	           |  (begin Expr* Expr)
;	           |  Lambda
;	           |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar Lambda]*) Expr)
;	           |  (prim Expr*)
;	           |  (Expr Expr*)
;   Lambda    --> (lambda (uvar*) Expr)
;   Immediate --> fixnum | () | #t | #f
;
; Output Language: 
;   Program   --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;	           |  (begin Expr* Expr)
;	           |  (let ([uvar Expr|Lambda]*) Expr)
;	           |  (letrec ([uvar Lambda]*) Expr)
;	           |  (prim Expr*)
;	           |  (Expr Expr*)
;   Lambda    --> (lambda (uvar*) Expr)
;   Immediate --> fixnum | () | #t | #f  
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who remove-anonymous-lambda
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  (define (lambda? lamb)
    (match lamb
      [(lambda (,fml* ...) ,ex) #t]
      [,x #f]))
  (define (Lambda rhs)
    (lambda (lamb)
      (match lamb
        [(lambda (,fml* ...) ,[(Expr #f) -> ex])
         (if rhs
             `(lambda (,fml* ...) ,ex)
             (let ([anon (unique-name 'anon)])
               `(letrec ([,anon (lambda (,fml* ...) ,ex)])
                  ,anon)))]
        [,x (error who "invalid Lambda ~s" x)])))
  (define (Expr rhs)
    (lambda (ex)
      (match ex
        [(begin ,[(Expr #f) -> ex*] ... ,[(Expr #f) -> ex])
         (make-begin `(,ex* ... ,ex))]
        [(if ,[(Expr #f) -> pred] ,[(Expr #f) -> conseq] ,[(Expr #f) -> alter])
         `(if ,pred ,conseq ,alter)]
        [(quote ,imm) `(quote ,imm)]
        [(let ([,uvar* ,[(Expr #t) -> ex*]] ...) ,[(Expr #f) -> ex])
         `(let ([,uvar* ,ex*] ...) ,ex)]
        [(letrec ([,uvar* ,[(Lambda #t) -> lamb*]] ...) ,[(Expr #f) -> ex])
         `(letrec ([,uvar* ,lamb*] ...) ,ex)]
        [(,prim ,ex* ...) (guard (memq prim primitives))
         `(,prim ,(map (Expr #f) ex*) ...)]
        [,lamb (guard (lambda? lamb)) ((Lambda rhs) lamb)]
        [,uvar (guard (uvar? uvar)) uvar]
        [(,[(Expr #f) -> rator] ,[(Expr #f) -> rand*] ...)
         `(,rator ,rand* ...)]
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (match x
      [,[(Expr #f) -> ex] ex])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   sanitize-binding-forms
;
; Description: 
;   This pass moves let bound lambda expressions to an outer
;   letrec binding. It also removes unnecessary let and letrec
;   forms when they contain no bindings.
;
; Input Language:  
;   Program   --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;	           |  (begin Expr* Expr)
;	           |  (let ([uvar Expr|Lambda]*) Expr)
;	           |  (letrec ([uvar Lambda]*) Expr)
;	           |  (prim Expr*)
;	           |  (Expr Expr*)
;   Lambda    --> (lambda (uvar*) Expr)
;   Immediate --> fixnum | () | #t | #f  
;
; Output Language: 
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
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who sanitize-binding-forms
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  (define (lambda? lamb)
    (match lamb
      [(lambda (,fml* ...) ,ex) #t]
      [,x #f]))
  (define (Lambda lamb)
    (match lamb
      [(lambda (,fml* ...) ,[Expr -> ex])
       `(lambda (,fml* ...) ,ex)]
      [,x (error who "invalid Lambda ~s" x)]))
  (define (Expr ex)
    (match ex
      [(begin ,[ex*] ... ,[ex])
       (make-begin `(,ex* ... ,ex))]
      [(if ,[pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(quote ,imm) `(quote ,imm)]
      [(let (,bnd* ...) ,[ex])
       (let ([lambnd* (filter (lambda (bnd) (lambda? (cadr bnd))) bnd*)])
         (let ([exbnd* (difference bnd* lambnd*)])
           (cond
             [(null? bnd*) ex]
             [(null? lambnd*) 
              `(let ([,(map car exbnd*) ,(map Expr (map cadr exbnd*))] ...) ,ex)]
             [(null? exbnd*) 
              `(letrec ([,(map car lambnd*) ,(map Lambda (map cadr lambnd*))] ...) ,ex)]
             [else
              `(letrec ([,(map car lambnd*) ,(map Lambda (map cadr lambnd*))] ...)
                 (let ([,(map car exbnd*) ,(map Expr (map cadr exbnd*))] ...)
                    ,ex))])))]
      [(letrec ([,uvar* ,[Lambda -> lamb*]] ...) ,[ex])
       (if (null? uvar*) ex `(letrec ([,uvar* ,lamb*] ...) ,ex))]
      [(,prim ,ex* ...) (guard (memq prim primitives))
       `(,prim ,(map Expr ex*) ...)]
      [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
      [,uvar (guard (uvar? uvar)) uvar]
      [,x (error who "invalid Expr ~s" x)]))
  (lambda (x)
    (match x
      [,[Expr -> ex] ex])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   optimize-known-call
;
; Description: 
;   This pass replaces the operator of an application with the 
;   label bound by the closure form when possible. Thus, this
;   is perofrmed in letrec form where each RHS and body of 
;   closure form is examined and transformed accordingly. The
;   output langugage doesn't change as this is an optimization
;   pass.
;
; Input Language:  
;   Program	  --> Expr
;   Expr      --> label
;              |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([label (lambda (uvar*)
;                                   (bind-free (uvar*) Expr))]*)
;                   (closures ([uvar label uvar*]*) Expr))
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
;              |  (letrec ([label (lambda (uvar*) 
;                                   (bind-free (uvar*) Expr))]*)
;                   (closures ([uvar label uvar*]*) Expr))
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
(define-who optimize-known-call
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  (define (Expr cbnd*)
    (lambda (ex)
      (match ex
        [(begin ,[ex*] ... ,[ex])
         (make-begin `(,ex* ... ,ex))]
        [(if ,[pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(quote ,imm) `(quote ,imm)]
        [(let ([,uvar* ,[ex*]] ...) ,[ex])
         `(let ([,uvar* ,ex*] ...) ,ex)]
        [(letrec ([,label* (lambda (,fml** ...) (bind-free (,f** ...) ,ex*))] ...)
           (closures ([,cp* ,lb* ,uvar** ...] ...) ,ex))
         (let ([cbnd* `((,cp* . ,lb*) ... ,cbnd* ...)])
           (let ([ex* (map (Expr cbnd*)  ex*)]
                 [ex ((Expr cbnd*) ex)])
             `(letrec ([,label* (lambda (,fml** ...) (bind-free (,f** ...) ,ex*))] ...)
                (closures ([,cp* ,lb* ,uvar** ...] ...) ,ex))))]
        [(,prim ,ex* ...) (guard (memq prim primitives)) 
         `(,prim ,(map (Expr cbnd*) ex*) ...)]
        [,uvar (guard (uvar? uvar)) uvar]
        [,label (guard (label? label)) label]
        [(,[rator] ,[rand*] ...)
         (if (uvar? rator)
             (let ([cbnd (assq rator cbnd*)])
               `(,(if cbnd (cdr cbnd) rator) ,rand* ...))
             `(,rator ,rand* ...))]
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (match x
      [,[(Expr '()) -> ex] ex])))
;---------------------------------------------------------------      