; Saliya Ekanayake
; sekanaya
; Assignment 12

;---------------------------------------------------------------
; Pass:           
;   optimize-source
;
; Description: 
;   Performs constant-folding, copy-propagation, 
;   useless-code-elimination, and dead-code-elimination.
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
(define-who optimize-source
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref
                        make-procedure procedure-ref procedure-code void
                        < <= = >= > boolean? eq? procedure? fixnum? null? pair? vector?
                        set-car! set-cdr! vector-set! procedure-set!)) 
  (define simple-binops `((+ . ,+) (- . ,-) (* . ,*) (< . ,<) (<= . ,<=)
                          (= . ,=) (>= . ,>=) (> . ,>) (eq? . ,eq?)))
  (define simple-unrops `((boolean? . ,boolean?) 
                          (fixnum? . ,(lambda (v) (and (integer? v) (exact? v) (fixnum-range? v))))
                          (null? . ,null?))) 
  (define effects '(set-car! set-cdr! vector-set! procedure-set!))
  
  ;; Environment related operations
  (define empty-env '())
  (define apply-env 
    (lambda (env x)
      (let ([bnd (assq x env)]) (if bnd (cdr bnd) #f))))
  (define extend-env
    (lambda (env bnd*)
      `(,@bnd* ,@env)))
  
  ;; Helper methods
  (define remove-common
    (lambda (s)
      (cond
        [(null? s) '()]
        [else (cons (car s) (remove-common (remq (car s) (cdr s))))])))
  (define (const? x)
    (match x
      [(quote ,imm) #t]
      [,x #f]))
  (define (const-value c)
    (match c
      [(quote ,imm) imm]))
  (define (any-true? l)
    (cond
      [(null? l) #f]
      [(car l) #t]
      [else (any-true? (cdr l))]))
  
  (define (handle-primitive x)
    (match x
      [(,prim . ((,ex1 (,ref1* ...) ,flag1) (,ex2 (,ref2* ...) ,flag2)))        
       (guard (assq prim simple-binops))
       (let ([ref* (remove-common `(,ref1* ... ,ref2* ...))]
             [flag (any-true? `(,flag1 ,flag2))])
         (if (and (const? ex1) (const? ex2))
             (let ([op (cdr (assq prim simple-binops))]
                   [v1 (const-value ex1)] [v2 (const-value ex2)])
               (cond
                 [(or (eq? prim '+) (eq? prim '*))
                  (let ([result (op v1 v2)])
                    (values (if (fixnum-range? result) 
                                `(quote ,result) `(,prim ,ex1 ,ex2)) '() #f))]
                 [else (values `(quote ,(op v1 v2)) '() #f)])) 
             (values `(,prim ,ex1 ,ex2) ref* flag)))]
      [(,prim .((,ex (,ref* ...) ,flag))) (guard (assq prim simple-unrops))
       (let ([ref* (remove-common ref*)])
         (if (const? ex)
             (let ([op? (cdr (assq prim simple-unrops))] [v (const-value ex)])
               (values `(quote ,(op? v)) '() #f))
             (values `(,prim ,ex) ref* flag)))]
      [(,prim . ((,ex* (,ref** ...) ,flag*) ...)) (guard (memq prim effects))
       (let ([ref* (remove-common `(,ref** ... ...))])
         (values `(,prim ,ex* ...) ref* #t))]
      [(,prim . ((,ex* (,ref** ...) ,flag*) ...))
       (let ([flag (any-true? flag*)]
             [ref* (remove-common `(,ref** ... ...))])
         (values `(,prim ,ex* ...) ref* flag))]))
  (define (Expr env)
    (lambda (ex)
      (match ex
        [(begin ,[ex* ref** flag*] ... ,[ex ref* flag])
         (let ([bnd* (map cdr (filter car `((,flag* . (,ex* . (,ref** ...))) ...)))])
           (values 
             (make-begin `(,(map car bnd*) ... ,ex))
             (remove-common `(,(map cdr bnd*) ... ... ,ref* ...))
             (if (null? bnd*) flag #t)))]
        [(if ,[p pref* pflag] ,[c cref* cflag] ,[a aref* aflag])
         (if (const? p)
             (if (eq? (const-value p) #f)
                 (values a (remove-common aref*) aflag)
                 (values c (remove-common cref*) cflag))
             (values `(if ,p ,c ,a)
               (remove-common `(,pref* ... ,cref* ... ,aref* ...))
               (or pflag cflag aflag)))]
        [(let ([,uvar* ,[ex* ref** flag*]] ...) ,ex)
         (let ([bnd* `((,uvar* . ,ex*) ...)] 
               [flagbnd* `((,uvar* . ,flag*) ...)]
               [refbnd* `((,uvar* . (,ref** ...)) ...)])
           ;; sub* is the possible copy propagated bindings to extend the env with
           (let ([sub* (filter (lambda (bnd)
                                 (or (const? (cdr bnd)) (uvar? (cdr bnd)))) bnd*)])
             (let-values ([(ex ref* flag) ((Expr (extend-env env sub*)) ex)])
               ;; Keep the binding only if its RHS expression has set its flag
               ;; or if LHS is in the referenced set of variables for let-body expression
               ;; The latter is true only because in a let binding the LHSs are visible
               ;; only inside the let body.
               (let ([bnd* (filter (lambda (bnd)
                                     (or (cdr (assq (car bnd) flagbnd*))
                                         (memq (car bnd) ref*))) bnd*)])
                 (values
                   (if (null? bnd*) ex 
                       `(let ([,(map car bnd*) ,(map cdr bnd*)] ...) ,ex))
                   (remove-common
                    `(,(map cdr (filter (lambda (refbnd)
                                 (assq (car refbnd) bnd*)) refbnd*)) ... ... 
                       ,(filter (lambda (ref) (not (assq ref bnd*))) ref*) ...))
                   (let ([flag* `(,(map (lambda (bnd)
                                          (cdr (assq (car bnd) flagbnd*))) bnd*) ...
                                   ,flag)])
                     (any-true? flag*)))))))]
        [(letrec ([,label* (lambda (,fml** ...) ,[ex* ref** flag*])] ...) ,[ex ref* flag])
         (let ([bnd* `((,label* . ((,fml** ...) ,ex* (,ref** ...) ,flag*)) ...)]
               [rhsref* (difference (remove-common `(,ref** ... ...)) `(,fml** ... ...))])
           (let ([bnd* (filter (lambda (bnd) 
                                 (or (memq (car bnd) ref*) (memq (car bnd) rhsref*))) bnd*)])
             ;; possible optimization when bnd* is null, then letrec is useless
             (let ([flag* `(,(map (lambda (bnd) (car (cddddr bnd))) bnd*) ... ,flag)]
                   [ref* (remove-common `(,(map cadddr bnd*) ... ... ,ref* ...))]
                   [label* (map car bnd*)]
                   [fml** (map cadr bnd*)]
                   [ex* (map caddr bnd*)])
               (values `(letrec ([,label* (lambda (,fml** ...) ,ex*)] ...) ,ex) ref*
                 (any-true? flag*)))))]
        [(quote ,imm) (values `(quote ,imm) '() #f)]
        [(,prim ,[ex* ref** flag*] ...) (guard (memq prim primitives))
         (handle-primitive `(,prim . ((,ex* (,ref** ...) ,flag*) ...)))]
        [(,[ex ref* flag] ,[ex* ref** flag*] ...)
         (values `(,ex ,ex* ...) (remove-common `(,ref* ... ,ref** ... ...)) #t)]
        [,uvar (guard (uvar? uvar))
         (let ([sub (apply-env env uvar)])
           (if sub (values sub (if (const? sub) '() `(,sub)) #f) 
               (values uvar `(,uvar) #f)))]
        [,label (guard (label? label))
         (values label `(,label) #f)]
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (match x
      [,[(Expr empty-env) -> ex ref* flag] ex])))
;---------------------------------------------------------------           
            