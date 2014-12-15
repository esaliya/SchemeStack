; Saliya Ekanayake
; sekanaya
; Assignment 14

;---------------------------------------------------------------
; Pass:           
;   convert-complex-datum
;
; Description: 
;   This pass converts complex datums, essentially quoted pairs
;   and vectors, into their primitive form. Pairs are converted
;   using cons and vectors are converted using make-vector and
;   vector-set!. The quoted pairs are move to a top level binding
;   to avoid unnecessary allocation and to keep the same pair in
;   recurring calls. However, it is possible to have two let 
;   bindings for two similar quoted datums when they were originally
;   defined in two distinct places of the code.
;
; Input Language:  
;   Program --> Expr
;   Expr    --> uvar
;            |  (quote datum)
;            |  (if Expr Expr Expr)
;            |  (begin Expr* Expr)
;            |  (lambda (uvar*) Expr)
;            |  (let ([uvar Expr]*) Expr)
;            |  (letrec ([uvar Expr]*) Expr)
;            |  (set! uvar Expr)
;            |  (prim Expr*)
;            |  (Expr Expr*)
;
;   A datum is an immediate, pair of datums, or vector of datums;
;   and an immediate is a boolean, a fixnum, or the empty list
;
; Output Language: 
;   Program --> Expr
;   Expr    --> uvar
;            |  (quote immediate)
;            |  (if Expr Expr Expr)
;            |  (begin Expr* Expr)
;            |  (lambda (uvar*) Expr)
;            |  (let ([uvar Expr]*) Expr)
;            |  (letrec ([uvar Expr]*) Expr)
;            |  (set! uvar Expr)
;            |  (prim Expr*)
;            |  (Expr Expr*)
;   An immediate is a boolean, a fixnum, or the empty list
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who convert-complex-datum
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  
  (define (immediate? imm)
    (or (and (integer? imm) (exact? imm) (fixnum-range? imm)) (memq imm '(#f #t ()))))
  
  (lambda (x)
    (define bnd* '())
    (define (add-bnd ex)
      (let ([t (unique-name 't)])
        (set! bnd* (cons `(,t ,ex) bnd*))
        t))
    (define (handle-datum d)
      (cond
        [(pair? d) `(cons ,(handle-datum (car d)) ,(handle-datum (cdr d)))]
        [(vector? d)
         (let ([tmp (unique-name 'tmp)] [n (sub1 (vector-length d))])
           `(let ([,tmp (make-vector (quote ,(vector-length d)))])
              ,(make-begin
                (let f ([idx 0])
                  (cons `(vector-set! ,tmp (quote ,idx) ,(handle-datum (vector-ref d idx)))
                        (if (< idx n) (f (add1 idx)) `(,tmp)))))))]
        [(immediate? d) `(quote ,d)]
        [else (error who "invalid datum ~s" d)]))
    (define (Expr ex)

      (match ex
        [(quote ,datum)
         (if (immediate? datum)
             `(quote ,datum)
             (add-bnd (handle-datum datum)))]
        [(begin ,[ex*] ... ,[ex])
         (make-begin `(,ex* ... ,ex))]
        [(if ,[pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(lambda (,fml* ...) ,[ex])
         `(lambda (,fml* ...) ,ex)]
        [(let ([,uvar* ,[ex*]] ...) ,[ex])
         `(let ([,uvar* ,ex*] ...) ,ex)]
        [(letrec ([,uvar* ,[ex*]] ...) ,[ex])
         `(letrec ([,uvar* ,ex*] ...) ,ex)]
        [(set! ,uvar ,[ex]) `(set! ,uvar ,ex)]
        [,uvar (guard (uvar? uvar)) uvar]
        [(,prim ,ex* ...) (guard (memq prim primitives))
         `(,prim ,(map Expr ex*) ...)]
        [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
        [,x (error who "invalid Expr ~s" x)]))
    (match x
      [,[Expr -> ex] (if (null? bnd*) ex `(let ,bnd* ,ex))])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   uncover-assigned
;
; Description: 
;   This pass uncovers all the assigned variables for lambda, let,
;   and letrec forms. The captured assigned variables are placed
;   in a new "assigned" form inside each of the particular three
;   forms. 
;
; Input Language:  
;   Program --> Expr
;   Expr    --> uvar
;            |  (quote immediate)
;            |  (if Expr Expr Expr)
;            |  (begin Expr* Expr)
;            |  (lambda (uvar*) Expr)
;            |  (let ([uvar Expr]*) Expr)
;            |  (letrec ([uvar Expr]*) Expr)
;            |  (set! uvar Expr)
;            |  (prim Expr*)
;            |  (Expr Expr*)
;
;   An immediate is a boolean, a fixnum, or the empty list
;
; Output Language: 
;   Program --> Expr
;   Expr    --> uvar
;            |  (quote immediate)
;            |  (if Expr Expr Expr)
;            |  (begin Expr* Expr)
;            |  (lambda (uvar*) (assigned (uvar*) Expr))
;            |  (let ([uvar Expr]*) (assigned (uvar*) Expr))
;            |  (letrec ([uvar Expr]*) (assigned (uvar*) Expr))
;            |  (set! uvar Expr)
;            |  (prim Expr*)
;            |  (Expr Expr*)
;
; An immediate is a boolean, a fixnum, or the empty list
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who uncover-assigned
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
      [(begin ,[ex* a**] ... ,[ex a*])
       (values (make-begin `(,ex* ... ,ex)) 
         (remove-common `(,a** ... ... ,a* ...)))]
      [(if ,[pred pa*] ,[conseq ca*] ,[alter aa*])
       (values `(if ,pred ,conseq ,alter) 
         (remove-common `(,pa* ... ,ca* ... ,aa* ...)))]
      [(let ([,uvar* ,[ex* a**]] ...) ,[ex a*])
       (let ([a* (intersection a* uvar*)]
             [rest* (remove-common `(,a** ... ... ,(difference a* uvar*) ...))])
         (values `(let ([,uvar* ,ex*] ...)
                    (assigned ,a* ,ex)) rest*))]
      [(letrec ([,uvar* ,[ex* a**]] ...) ,[ex a*])
       (let ([t* (remove-common `(,a** ... ... ,a* ...))])
         (let ([a* (intersection t* uvar*)] [rest* (difference t* uvar*)])
           (values `(letrec ([,uvar* ,ex*] ...) (assigned ,a* ,ex)) rest*)))]
      [(lambda (,fml* ...) ,[ex a*])
       (let ([a* (intersection a* fml*)] [rest* (difference a* fml*)])
         (values `(lambda (,fml* ...) (assigned ,a* ,ex)) rest*))]
      [(set! ,uvar ,[ex a*])
       (values `(set! ,uvar ,ex) (remove-common `(,uvar ,a* ...)))]
      [(quote ,imm) (values `(quote ,imm) '())]
      [,uvar (guard (uvar? uvar)) (values uvar `())]
      [(,prim ,[ex* a**] ...) (guard (memq prim primitives))
       (values `(,prim ,ex* ...) (remove-common `(,a** ... ...)))]
      [(,[rator a*] ,[rand* a**] ...)
       (values `(,rator ,rand* ...) (remove-common `(,a* ... ,a** ... ...)))]
      [,x (error who "invalid Expr ~S" x)]))
  (lambda (x)
    (match x
      [,[Expr -> ex a*] 
        (if (null? a*) ex 
            (error who "Assigned variables cannot appear in top level ~s" a*))])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   purify-letrec
;
; Description: 
;   This pass removes "impure" bindings from letrec expressions
;   and make them simply contain pure lambda bindings. The passde
;   separately handles pure letrect forms. The algorithm used is
;   the simple version given in the assignment, which has the 
;   tendency to bloat the code with unncessary assignments.
;
; Input Language:  
;   Program --> Expr
;   Expr    --> uvar
;            |  (quote immediate)
;            |  (if Expr Expr Expr)
;            |  (begin Expr* Expr)
;            |  (lambda (uvar*) (assigned (uvar*) Expr))
;            |  (let ([uvar Expr]*) (assigned (uvar*) Expr))
;            |  (letrec ([uvar Expr]*) (assigned (uvar*) Expr))
;            |  (set! uvar Expr)
;            |  (prim Expr*)
;            |  (Expr Expr*)
;
;   An immediate is a boolean, a fixnum, or the empty list
;
; Output Language: 
;   Program --> Expr
;   Expr    --> uvar
;            |  (quote immediate)
;            |  (if Expr Expr Expr)
;            |  (begin Expr* Expr)
;            |  Lambda
;            |  (let ([uvar Expr]*) (assigned (uvar*) Expr))
;            |  (letrec ([uvar Lambda]*) Expr)
;            |  (set! uvar Expr)
;            |  (prim Expr*)
;            |  (Expr Expr*)
;   Lambda  --> (lambda (uvar*) (assigned (uvar*) Expr))
;
;   An immediate is a boolean, a fixnum, or the empty list
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who purify-letrec
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  (define (Expr ex)
    (match ex
      [(begin ,[ex*] ... ,[ex])
       (make-begin `(,ex* ... ,ex))]
      [(if ,[pred] ,[conseq] ,[alter])
       `(if ,pred ,conseq ,alter)]
      [(quote ,imm) `(quote ,imm)]
      [,uvar (guard (uvar? uvar)) uvar]
      [(lambda (,fml* ...) (assigned (,a* ...) ,[ex]))
       `(lambda (,fml* ...) (assigned (,a* ...) ,ex))]
      [(let ([,uvar* ,[ex*]] ...) (assigned (,a* ...) ,[ex]))
       `(let ([,uvar* ,ex*] ...) (assigned (,a* ...) ,ex))]
      ;; Handle pure letrec separately
      [(letrec ([,uvar* (lambda (,fml** ...) 
                           (assigned (,a** ...) ,[ex*]))] ...)
         (assigned () ,[ex]))
       `(letrec ([,uvar* (lambda (,fml** ...) 
                           (assigned (,a** ...) ,ex*))] ...) ,ex)]
      ;; Handle impure letrec based on the simple algorithm
      [(letrec ([,uvar* ,[ex*]] ...) (assigned (,a* ...) ,[ex]))
       (let ([t* (map (lambda (x) (unique-name 't)) uvar*)])
         `(let ([,uvar* (void)] ...)
            (assigned (,uvar* ...)
              ,(make-begin
                 `((let ([,t* ,ex*] ...)
                     (assigned ()
                       ,(make-begin `((set! ,uvar* ,t*) ...))))
                   ,ex)))))]
      [(set! ,uvar ,[ex]) `(set! ,uvar ,ex)]
      [(,prim ,ex* ...) (guard (memq prim primitives))
       `(,prim ,(map Expr ex*) ...)]
      [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
      [,x (error who "invalid Expr ~s" x)]))
  (lambda (x)
    (match x
      [,[Expr -> ex] ex])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   convert-assignments
;
; Description: 
;   This pass gets rid of assignments by converting their form
;   into set-car!. Eventually, this results in marking the
;   locations for assignments explicit and enables sharing of
;   such locations through procedure bounderies.
;
; Input Language:  
;   Program --> Expr
;   Expr    --> uvar
;            |  (quote immediate)
;            |  (if Expr Expr Expr)
;            |  (begin Expr* Expr)
;            |  Lambda
;            |  (let ([uvar Expr]*) (assigned (uvar*) Expr))
;            |  (letrec ([uvar Lambda]*) Expr)
;            |  (set! uvar Expr)
;            |  (prim Expr*)
;            |  (Expr Expr*)
;   Lambda  --> (lambda (uvar*) (assigned (uvar*) Expr))
;
;   An immediate is a boolean, a fixnum, or the empty list
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
(define-who convert-assignments
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                  < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                  set-car! set-cdr! vector-set!))
  (define (lambda? lamb)
    (match lamb
      [(lambda (,fml* ...) (assigned (,a* ...) ,ex)) #t]
      [,x #f]))
  (define (Lambda a*)
    (lambda (lamb)
      (match lamb
        [(lambda (,fml* ...) (assigned (,as* ...) ,ex))
         (if (null? as*)
             `(lambda (,fml* ...) ,((Expr a*) ex))
             (let ([tb* (map (lambda (as) `(,as . ,(unique-name 't))) as*)])
               (let ([fml* (map (lambda (fml)
                                  (let ([tb (assq fml tb*)])
                                    (if tb (cdr tb) fml))) fml*)])
                 `(lambda (,fml* ...)
                    (let ([,(map car tb*) (cons ,(map cdr tb*) (void))] ...)
                      ,((Expr `(,a* ... ,as* ...)) ex))))))])))
  (define (Expr a*)
    (lambda (ex)
      (match ex
        [(begin ,[ef*] ... ,[ef])
         (make-begin `(,ef* ... ,ef))]
        [(if ,[pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(quote ,imm) `(quote ,imm)]
        [(letrec ([,uvar* ,[(Lambda a*) -> lamb*]] ...) ,[ex])
         `(letrec ([,uvar* ,lamb*] ...) ,ex)]
        [(let ([,uvar* ,[ex*]] ...) (assigned (,as* ...) ,ex))
         (if (null? as*)
             `(let ([,uvar* ,ex*] ...) ,((Expr a*) ex))
             (let ([tb* (map (lambda (as) `(,as . ,(unique-name 't))) as*)])
               (let ([uvar* (map (lambda (uvar)
                                   (let ([tb (assq uvar tb*)])
                                     (if tb (cdr tb) uvar))) uvar*)])
                 `(let ([,uvar* ,ex*] ...)
                    (let ([,(map car tb*) (cons ,(map cdr tb*) (void))] ...)
                      ,((Expr `(,a* ... ,as* ...)) ex))))))]
        [(set! ,uvar ,[ex]) `(set-car! ,uvar ,ex)]
        [,uvar (guard (uvar? uvar))
         (if (memq uvar a*) `(car ,uvar) uvar)]
        [,lamb (guard (lambda? lamb)) 
          ((Lambda a*) lamb)]
        [(,prim ,ex* ...) (guard (memq prim primitives))
         `(,prim ,(map (Expr a*) ex*) ...)]
        [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
        
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (match x
      [,[(Expr '()) -> ex] ex]))) 
;---------------------------------------------------------------