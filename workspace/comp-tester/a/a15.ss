; Saliya Ekanayake
; sekanaya
; Assignment 15

; Note. verify-a11-output, verify-a10-output, analyze-closure-size
;       are borrowed from assignments' descriptions

;---------------------------------------------------------------
; Pass:           
;   parse-scheme
;
; Description: 
;   This pass verifies and parses input grammar into the output
;   grammar. It converts variables into unique variables with
;   usual shadowing rules. Also converts one-armed 'if, 'and, 'or
;   into forms understood by the output grammar. Morevoer unquoted
;   constants are converted to quoted constants. The implicit begins
;   of lambda, let, and letrec bodies are converted to explicit begin
;   expressions.
;
; Input Language:  
;   Program --> Expr
;   Expr    --> constant
;            | var
;            | (quote datum)
;            | (if Expr Expr)
;            | (if Expr Expr Expr)
;            | (and Expr*)
;            | (or Expr*)
;            | (begin Expr* Expr)
;            | (lambda (var*) Expr+)
;            | (let ([var Expr]*) Expr+)
;            | (letrec ([var Expr]*) Expr+)
;            | (set! var Expr)
;            | (prim Expr*)
;            | (Expr Expr*)
;
;   where:
;        * constant is #t, #f, (), or a fixnum;
;        * fixnum is an exact integer;
;        * datum is a constant, pair of datums, or vector of datums; and
;        * var is an arbitrary symbol. 
;        * primitives are,
;            void (zero arguments); car, cdr, vector-length,
;            make-vector, boolean?, fixnum?, null?, pair?, procedure?,
;            vector? (one argument); *, +, -, cons, vector-ref, <, <=, =,
;            >=, >, eq?, set-car!, set-cdr! (two arguments); and vector-set!
;           (three arguments).
;
;
; Output Language: 
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
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;   
;   A datum is an immediate, pair of datums, or vector of datums;
;   and an immediate is a boolean, a fixnum, or the empty list
;--------------------------------------------------------------- 
(define-who parse-scheme
  (define (constant? x)
    (or (memq x '(#t #f ()))
        (and (and (integer? x) (exact? x))
             (or (fixnum-range? x)
                 (error who "integer ~s is out of fixnum range" x)))))
  (define (datum? x)
    (or (constant? x)
        (if (pair? x)
            (and (datum? (car x)) (datum? (cdr x)))
            (and (vector? x) (andmap datum? (vector->list x))))))
  (define (verify-var-list x*)
    (let loop ([x* x*])
      (unless (null? x*)
        (let ([x (car x*)] [x* (cdr x*)])
          (unless (symbol? x)
            (error who "invalid Var ~s" x))
          (when (memq x x*)
            (error who "duplicate Var ~s" x))
          (loop x*)))))

  (define (lookup id env)
    (let ([action (assq id env)])
      (if action (cdr action) (error who "unbound variable ~s" id))))
  
  (define (Var-action v)
    (let ([v (unique-name v)])
      (lambda (env x)
        (match x
          [,id (guard (symbol? id)) v]
          [(,id ,[(Expr env) -> x*] ...) (guard (symbol? id)) `(,v ,x* ...)]
          [,x (error who "invalid Expr ~s" x)]))))
  (define (Application env x)
    (match x
      [(,[(Expr env) -> x] ,[(Expr env) -> x*] ...) `(,x ,x* ...)]
      [,x (error who "invalid Expr ~s" x)]))
           
  (define initial-env 
    ;; Keyword handlers
    `((quote . ,(lambda (env x)
                  (match x
                    [(quote ,datum)
                     (unless (datum? datum)
                       (error who "invalid datum ~s" datum))
                     `(quote ,datum)]
                    [,x (error who "invalid Expr ~s" x)])))
      (and . ,(lambda (env x)
                (match x
                  [(and ,[(Expr env) -> x*] ...)
                   (if (null? x*)
                       '(quote #t)
                       (let f ([x* x*])
                         (let ([x (car x*)] [x* (cdr x*)])
                           (if (null? x*)
                               x
                               `(if ,x ,(f x*) (quote #f))))))]
                  [,x (error who "invalid Expr ~s" x)])))
      (or . ,(lambda (env x)
               (match x
                 [(or ,[(Expr env) -> x*] ...)
                  (if (null? x*)
                      '(quote #f)
                      (let f ([x* x*])
                        (let ([x (car x*)] [x* (cdr x*)])
                          (if (null? x*)
                              x
                              (let ([t (unique-name 't)])
                                `(let ([,t ,x])
                                   (if ,t ,t ,(f x*))))))))]
                 [,x (error who "invalid Expr ~s" x)])))
      (if . ,(lambda (env x)
               (match x
                 [(if ,[(Expr env) -> pred] ,[(Expr env) -> conseq] ,[(Expr env) -> alter])
                  `(if ,pred ,conseq ,alter)]
                 [(if ,[(Expr env) -> pred] ,[(Expr env) -> conseq])
                  `(if ,pred ,conseq (void))]
                 [,x (error who "invalid Expr ~s" x)])))
      (begin . ,(lambda (env x)
                  (match x
                    [(begin ,[(Expr env) -> x*] ... ,[(Expr env) -> x])
                     (make-begin `(,x* ... ,x))]
                    [,x (error who "invalid Expr ~s" x)])))
      (set! . ,(lambda (env x)
                 (match x
                   [(set! ,id ,[(Expr env) -> x]) (guard (symbol? id))
                    `(set! ,((Expr env) id) ,x)]
                   [,x (error who "invalid Expr ~s" x)])))
      (lambda . ,(lambda (env x)
                   (match x
                     [(lambda (,fml* ...) ,x ,x* ...)
                      (verify-var-list fml*)
                      (let ([env (append (map (lambda (fml)
                                                `(,fml . ,(Var-action fml))) fml*) env)])
                        (let ([x ((Expr env) x)] [x* (map (Expr env) x*)])
                          `(lambda (,(map (lambda (fml)
                                            ((lookup fml env) env fml)) fml*) ...)
                             ,(make-begin `(,x ,x* ...)))))]
                     [,x (error who "invalid Expr ~s" x)])))
      (let . ,(lambda (env x)
                (match x
                  [(let ([,var* ,[(Expr env) -> rhs*]] ...) ,x ,x* ...)
                   (verify-var-list var*)
                   (let ([env (append (map (lambda (var)
                                             `(,var . ,(Var-action var))) var*) env)])
                     (let ([x ((Expr env) x)] [x* (map (Expr env) x*)])
                       `(let ([,(map (lambda (var)
                                       ((lookup var env) env var)) var*) ,rhs*] ...)
                          ,(make-begin `(,x ,x* ...)))))]
                  [,x (error who "invalid Expr ~s" x)])))
      (letrec . ,(lambda (env x)
                   (match x
                     [(letrec ([,var* ,rhs*] ...) ,x ,x* ...)
                      (verify-var-list var*)
                      (let ([env (append (map (lambda (var)
                                             `(,var . ,(Var-action var))) var*) env)])
                        (let ([rhs* (map (Expr env) rhs*)]
                              [x ((Expr env) x)]
                              [x* (map (Expr env) x*)])
                          `(letrec ([,(map (lambda (var)
                                             ((lookup var env) env var)) var*) ,rhs*] ...)
                             ,(make-begin `(,x ,x* ...)))))]
                     [,x (error who "invalid Expr ~s" x)])))
      
      ;; Primitive handlers
      (not . ,(lambda (env x)
                (match x
                  [(not ,[(Expr env) -> x])
                   `(if ,x (quote #f) (quote #t))]
                  [,x (error who "invalid Expr ~s" x)])))
      (void . ,(lambda (env x)
                 (match x
                   [(void) '(void)]
                   [,x (error who "invalid Expr ~s" x)])))
      (+ . ,(lambda (env x)
              (match x
                [(+ ,[(Expr env) -> x] ,[(Expr env) -> y]) `(+ ,x ,y)]
                [,x (error who "invalid Expr ~s" x)])))
      (- . ,(lambda (env x)
              (match x
                [(- ,[(Expr env) -> x] ,[(Expr env) -> y]) `(- ,x ,y)]
                [,x (error who "invalid Expr ~s" x)])))
      (* . ,(lambda (env x)
              (match x
                [(* ,[(Expr env) -> x] ,[(Expr env) -> y]) `(* ,x ,y)]
                [,x (error who "invalid Expr ~s" x)])))
      (<= . ,(lambda (env x)
               (match x
                 [(<= ,[(Expr env) -> x] ,[(Expr env) -> y]) `(<= ,x ,y)]
                 [,x (error who "invalid Expr ~s" x)])))
      (< . ,(lambda (env x)
              (match x
                [(< ,[(Expr env) -> x] ,[(Expr env) -> y]) `(< ,x ,y)]
                [,x (error who "invalid Expr ~s" x)])))
      (= . ,(lambda (env x)
              (match x
                [(= ,[(Expr env) -> x] ,[(Expr env) -> y]) `(= ,x ,y)]
                [,x (error who "invalid Expr ~s" x)])))
      (>= . ,(lambda (env x)
               (match x
                 [(>= ,[(Expr env) -> x] ,[(Expr env) -> y]) `(>= ,x ,y)]
                 [,x (error who "invalid Expr ~s" x)])))
      (> . ,(lambda (env x)
              (match x
                [(> ,[(Expr env) -> x] ,[(Expr env) -> y]) `(> ,x ,y)]
                [,x (error who "invalid Expr ~s" x)])))
      (boolean? . ,(lambda (env x)
                     (match x
                       [(boolean? ,[(Expr env) -> x] ) `(boolean? ,x)]
                       [,x (error who "invalid Expr ~s" x)])))
      (car . ,(lambda (env x)
                (match x
                  [(car ,[(Expr env) -> x] ) `(car ,x)]
                  [,x (error who "invalid Expr ~s" x)])))
      (cdr . ,(lambda (env x)
                (match x
                  [(cdr ,[(Expr env) -> x] ) `(cdr ,x)]
                  [,x (error who "invalid Expr ~s" x)])))
      (cons . ,(lambda (env x)
                 (match x
                   [(cons ,[(Expr env) -> x] ,[(Expr env) -> y]) `(cons ,x ,y)]
                   [,x (error who "invalid Expr ~s" x)])))
      (eq? . ,(lambda (env x)
                (match x
                  [(eq? ,[(Expr env) -> x] ,[(Expr env) -> y]) `(eq? ,x ,y)]
                  [,x (error who "invalid Expr ~s" x)])))
      (fixnum? . ,(lambda (env x)
                    (match x
                      [(fixnum? ,[(Expr env) -> x]) `(fixnum? ,x)]
                      [,x (error who "invalid Expr ~s" x)])))
      (make-vector . ,(lambda (env x)
                        (match x
                          [(make-vector ,[(Expr env) -> x]) `(make-vector ,x)]
                          [,x (error who "invalid Expr ~s" x)])))
      (null? . ,(lambda (env x)
                  (match x
                    [(null? ,[(Expr env) -> x]) `(null? ,x)]
                    [,x (error who "invalid Expr ~s" x)])))
      (pair? . ,(lambda (env x)
                  (match x
                    [(pair? ,[(Expr env) -> x]) `(pair? ,x)]
                    [,x (error who "invalid Expr ~s" x)])))
      (procedure? . ,(lambda (env x)
                       (match x
                         [(procedure? ,[(Expr env) -> x]) `(procedure? ,x)]
                         [,x (error who "invalid Expr ~s" x)])))
      (set-car! . ,(lambda (env x)
                     (match x
                       [(set-car! ,[(Expr env) -> x] ,[(Expr env) -> y])
                        `(set-car! ,x ,y)]
                       [,x (error who "invalid Expr ~s" x)])))
      (set-cdr! . ,(lambda (env x)
                     (match x
                       [(set-cdr! ,[(Expr env) -> x] ,[(Expr env) -> y])
                        `(set-cdr! ,x ,y)]
                       [,x (error who "invalid Expr ~s" x)])))
      (vector? . ,(lambda (env x)
                    (match x
                      [(vector? ,[(Expr env) -> x]) `(vector? ,x)]
                      [,x (error who "invalid Expr ~s" x)])))
      (vector-length . ,(lambda (env x)
                          (match x
                            [(vector-length ,[(Expr env) -> x])
                             `(vector-length ,x)]
                            [,x (error who "invalid Expr ~s" x)])))
      (vector-ref . ,(lambda (env x)
                       (match x
                         [(vector-ref ,[(Expr env) -> x] ,[(Expr env) -> y])
                          `(vector-ref ,x ,y)]
                         [,x (error who "invalid Expr ~s" x)])))
      (vector-set! . ,(lambda (env x)
                        (match x
                          [(vector-set! ,[(Expr env) -> x] ,[(Expr env) -> y] ,[(Expr env) -> z])
                           `(vector-set! ,x ,y ,z)]
                          [,x (error who "invalid Expr ~s" x)])))
      ))
                     
  (define Expr
    (lambda (env)
      (lambda (x)
        (match x
          [,k (guard (constant? k)) `(quote ,k)]
          [,id (guard (symbol? id)) ((lookup id env) env id)]
          [(,id . ,stuff)
           (guard (symbol? id))
           ((lookup id env) env `(,id . ,stuff))]
          [(,x . ,stuff) (Application env `(,x . ,stuff))]
          [,x (error who "invalid Expr ~s" x)]))))
  (lambda (x)
    (match x
      [,[(Expr initial-env) -> ex] ex])))
;---------------------------------------------------------------


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
;   such locations through procedure boundaries.
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
;              |  (begin Expr* Expr)
;              |  Lambda
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar Lambda]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
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
;              |  (begin Expr* Expr)
;              |  Lambda
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar Lambda]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Lambda    --> (lambda (uvar*) Expr)
;   Immediate --> fixnum | () | #t | #f
;
; Output Language: 
;   Program   --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  Lambda
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar Lambda]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
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
;              |  (begin Expr* Expr)
;              |  Lambda
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([uvar Lambda]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Lambda    --> (lambda (uvar*) Expr)
;   Immediate --> fixnum | () | #t | #f
;
; Output Language: 
;   Program   --> Expr
;   Expr      --> uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr|Lambda]*) Expr)
;              |  (letrec ([uvar Lambda]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
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
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr|Lambda]*) Expr)
;              |  (letrec ([uvar Lambda]*) Expr)
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Lambda    --> (lambda (uvar*) Expr)
;   Immediate --> fixnum | () | #t | #f  
;
; Output Language: 
;   Program   --> Expr
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
;   Program   --> Expr
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
;   Program   --> Expr
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


;---------------------------------------------------------------
; Pass:           
;   uncover-free
;
; Description: 
;   Finds all the free variables for lambda expressions and
;   record them in the new form 'free' inside lambda.
;
; Input Language:  
;   Program   --> Expr
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
;   Program   --> Expr
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
;   throughout to make it possible for later passes to retrieve
;   the free variables by giving the index from the listed order.
;   
;   The closures form introduced for the body of letrec expressions
;   captures the assocation of the unique variable, which was bound
;   to the procedure in the source language, and the unique label
;   used to represent the particular procedure in later passes along
;   with its free variables.
;
; Input Language:  
;   Program   --> Expr
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
;   Program   --> Expr
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
;   Program   --> Expr
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
;   Program   --> Expr
;   Expr      --> label
;              |  uvar
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
;   Program   --> Expr
;   Expr      --> label
;              |  uvar
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
;   Program   --> (letrec ([label (lambda (uvar*) Expr)]*) Expr)
;   Expr      --> label
;              |  uvar
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
;   Program  --> (letrec ([label (lambda (uvar*) Expr)]*) Expr)
;   Expr      --> label
;           |  uvar
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
;   Program-->(letrec ([label (lambda (uvar*) Value)]*) Value)
;   Value-->label
;            |uvar
;            |(quote Immediate)
;            |(if Pred Value Value)
;            |(begin Effect* Value)
;            |(let ([uvar Value]*) Value)
;            |(value-prim Value*)
;            |(Value Value*)
;   Pred-->(true)
;            |(false)
;            |(if Pred Pred Pred)
;            |(begin Effect* Pred)
;            |(let ([uvar Value]*) Pred)
;            |(pred-prim Value*)
;   Effect-->(nop)
;            |(if Pred Effect Effect)
;            |(begin Effect* Effect)
;            |(let ([uvar Value]*) Effect)
;            |(effect-prim Value*)
;            |(Value Value*)
;   Immediate-->fixnum | () | #t | #f
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
;   Program-->(letrec ([label (lambda (uvar*) Value)]*) Value)
;   Value-->label
;            |uvar
;            |(quote Immediate)
;            |(if Pred Value Value)
;            |(begin Effect* Value)
;            |(let ([uvar Value]*) Value)
;            |(value-prim Value*)
;            |(Value Value*)
;   Pred-->(true)
;            |(false)
;            |(if Pred Pred Pred)
;            |(begin Effect* Pred)
;            |(let ([uvar Value]*) Pred)
;            |(pred-prim Value*)
;   Effect-->(nop)
;            |(if Pred Effect Effect)
;            |(begin Effect* Effect)
;            |(let ([uvar Value]*) Effect)
;            |(effect-prim Value*)
;            |(Value Value*)
;   Immediate-->fixnum | () | #t | #f
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
;   Program-->(letrec ([label (lambda (uvar*) Tail)]*) Tail)
;   Tail-->Triv
;         |(alloc Value)
;         |(binop Value Value)
;         |(Value Value*)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;            |  (let ([uvar Value]*) Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Value Value)
;            |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;            |  (let ([uvar Value]*) Pred)
;  Effect-->(nop)
;         |(mset! Value Value Value)
;            |  (Value Value*)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;            |  (let ([uvar Value]*) Effect)
;  Value-->Triv
;         |(alloc Value)
;         |(binop Value Value)
;            |  (Value Value*)
;         |(if Pred Value Value)
;         |(begin Effect* Value)
;            |  (let ([uvar Value]*) Value)
;   Triv-->uvar | int | label 
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


; Note. Burrowed from assignment description/resources
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


; Note. Borrowed from assignment description/resources
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
;   Program --> (letrec ([label (lambda () Tail)]*) Tail)
;   Tail    --> (Triv)
;            |  (if (relop Triv Triv) (,label) (,label))
;            |  (begin Effect* Tail)
;   Effect  --> (set! Loc Triv)
;            |  (set! Loc (binop Triv Triv))
;   Loc     --> reg | disp-opnd | index-opnd
;   Triv    --> Loc | int | label 
;
; Output Language: 
;   Program --> (letrec ([label (lambda () Tail)]*) Tail)
;   Tail    --> (Triv)
;            |  (if (relop Triv Triv) (,label) (,label))
;            |  (begin Effect* Tail)
;   Effect  --> (set! Loc Triv)
;            |  (set! Loc (binop Triv Triv))
;   Loc     --> reg | disp-opnd | index-opnd
;   Triv    --> Loc | int | label
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


;---------------------------------------------------------------
; Pass:           
;   uncover-locals
;
; Description: 
;   This pass will record all the variables 
;   bound by let expressions inside locals form
;
; Input Language:  
;   Program --> (letrec ([label (lambda (uvar*) Tail)]*) Tail)
;   Tail    --> Triv
;            | (alloc Value)
;            | (binop Value Value)
;            | (Value Value*)
;            | (if Pred Tail Tail)
;            | (begin Effect* Tail)
;            | (let ([uvar Value]*) Tail)
;   Pred    -->(true)
;            | (false)
;            | (relop Value Value)
;            | (if Pred Pred Pred)
;            | (begin Effect* Pred)
;            | (let ([uvar Value]*) Pred)
;  Effect   -->(nop)
;            | (mset! Value Value Value)
;            | (Value Value*)
;            | (if Pred Effect Effect)
;            | (begin Effect* Effect)
;            | (let ([uvar Value]*) Effect)
;  Value    --> Triv
;            | (alloc Value)
;            | (binop Value Value)
;            | (Value Value*)
;            | (if Pred Value Value)
;            | (begin Effect* Value)
;            | (let ([uvar Value]*) Value)
;   Triv   --> uvar | int | label 
;
; Output Language: 
;   Program --> (letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body    --> (locals (uvar*) Tail)
;   Tail    --> Triv
;            | (alloc Value)
;            | (binop Value Value)
;            | (Value Value*)
;            | (if Pred Tail Tail)
;            | (begin Effect* Tail)
;            | (let ([uvar Value]*) Tail)
;   Pred    -->(true)
;            | (false)
;            | (relop Value Value)
;            | (if Pred Pred Pred)
;            | (begin Effect* Pred)
;            | (let ([uvar Value]*) Pred)
;  Effect   -->(nop)
;            | (mset! Value Value Value)
;            | (Value Value*)
;            | (if Pred Effect Effect)
;            | (begin Effect* Effect)
;            | (let ([uvar Value]*) Effect)
;  Value    --> Triv
;            | (alloc Value)
;            | (binop Value Value)
;            | (Value Value*)
;            | (if Pred Value Value)
;            | (begin Effect* Value)
;            | (let ([uvar Value]*) Value)
;   Triv    --> uvar | int | label 
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
;   Program --> (letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body --> (locals (uvar*) Tail)
;   Tail --> Triv
;          | (alloc Value)
;          | (binop Value Value)
;          | (Value Value*)
;          | (if Pred Tail Tail)
;          | (begin Effect* Tail)
;          | (let ([uvar Value]*) Tail)
;   Pred --> (true)
;          | (false)
;          | (relop Value Value)
;          | (if Pred Pred Pred)
;          | (begin Effect* Pred)
;          | (let ([uvar Value]*) Pred)
;  Effect--> (nop)
;          | (mset! Value Value Value)
;          | (Value Value*)
;          | (if Pred Effect Effect)
;          | (begin Effect* Effect)
;          |  (let ([uvar Value]*) Effect)
;  Value --> Triv
;          | (alloc Value)
;          | (binop Value Value)
;          | (Value Value*)
;          | (if Pred Value Value)
;          | (begin Effect* Value)
;          | (let ([uvar Value]*) Value)
;   Triv --> uvar | int | label 
;
; Output Language: 
;   Program --> (letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body --> (locals (uvar*) Tail)
;   Tail --> Triv
;          | (alloc Value)
;          | (mref Value Value)
;          | (binop Value Value)
;          | (Value Value*)
;          | (if Pred Tail Tail)
;          | (begin Effect* Tail)
;   Pred --> (true)
;          | (false)
;          | (relop Value Value)
;          | (if Pred Pred Pred)
;          | (begin Effect* Pred)
;  Effect --> (nop)
;          | (set! uvar Value)
;          | (mset! Value Value Value)
;          |  (Value Value*)
;          | (if Pred Effect Effect)
;          | (begin Effect* Effect)
;  Value --> Triv
;          | (alloc Value)
;          | (mref Value Value)
;          | (binop Value Value)
;          |  (Value Value*)
;          | (if Pred Value Value)
;          | (begin Effect* Value)
;   Triv --> uvar | int | label 
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


;---------------------------------------------------------------
; Enter into UIL
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


; Note. Modified the given verifier in assignment 7
;---------------------------------------------------------------
; Pass: verify-uil 
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
;   Program-->(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body-->(locals (uvar*) Tail)
;   Tail-->Triv
;         |(alloc Value)
;         |(mref Value Value)
;         |(binop Value Value)
;         |(Value Value*)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Value Value)
;         |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;  Effect-->(nop)
;         |(set! uvar Value)
;         |(mset! Value Value Value)
;         |  (Value Value*)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;  Value-->Triv
;         |(alloc Value)
;         |(mref Value Value)
;         |(binop Value Value)
;         |  (Value Value*)
;         |(if Pred Value Value)
;         |(begin Effect* Value)
;   Triv-->uvar | int | label 
;
; Output Language: 
;   Program-->(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body-->(locals (uvar*) Tail)
;   Tail-->Triv
;         |(alloc Triv)
;         |(mref Triv Triv)
;         |(binop Triv Triv)
;         |(Triv Triv*)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;         |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;  Effect-->(nop)
;         |(set! uvar Value)
;         |(mset! Triv Triv Triv)
;         |(Triv Triv*)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;  Value-->Triv
;         |(alloc Triv)
;         |(mref Triv Triv)
;         |(binop Triv Triv)
;         |(if Pred Value Value)
;         |(begin Effect* Value)
;         |(Triv Triv*)
;   Triv-->uvar | int | label
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
;   Program-->(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body-->(locals (uvar*) Tail)
;   Tail-->Triv
;         |(alloc Triv)
;         |(mref Triv Triv)
;         |(binop Triv Triv)
;         |(Triv Triv*)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;         |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;  Effect-->(nop)
;         |(set! uvar Value)
;         |(mset! Triv Triv Triv)
;         |  (Triv Triv*)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;  Value-->Triv
;         |(alloc Triv)
;         |(mref Triv Triv)
;         |(binop Triv Triv)
;         |(if Pred Value Value)
;         |(begin Effect* Value)
;         |  (Triv Triv*)
;   Triv-->uvar | int | label
;
; Output Language: 
;   Program-->(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body-->(locals (uvar*) Tail)
;   Tail-->Triv
;         |(alloc Triv)
;         |(mref Triv Triv)
;         |(binop Triv Triv)
;         |(Triv Triv*)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;         |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;  Effect-->(nop)
;         |(set! uvar Triv)
;         |(set! uvar (binop Triv Triv))
;         |(set! uvar (Triv Triv*))
;         |(set! uvar (alloc Triv))
;         |(set! uvar (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;         |(Triv Triv*)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Triv-->uvar | int | label
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
;   Program-->(letrec ([label (lambda (uvar*) Body)]*) Body)
;   Body-->(locals (uvar*) Tail)
;   Tail-->Triv
;         |(alloc Triv)
;         |(mref Triv Triv)
;         |(binop Triv Triv)
;         |(Triv Triv*)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;         |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;  Effect-->(nop)
;         |(set! uvar Triv)
;         |(set! uvar (binop Triv Triv))
;         |(set! uvar (Triv Triv*))
;         |(set! uvar (alloc Triv))
;         |(set! uvar (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;         |  (Triv Triv*)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Triv-->uvar | int | label
;
; Output Language:
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   
;   Body-->(locals (uvar*) (new-frames (Frame*) Tail))
;   
;   Frame--> (uvar*)
;   
;   Tail-->(Triv Loc*)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;         |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;   Effect-->(nop)
;         |(set! Var Triv)
;         |(set! Var (binop Triv Triv))
;         |(set! Var (alloc Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;         |(return-point label Tail)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Loc  -->reg | fvar
;   Var  -->uvar | Loc
;   Triv -->Var | int | label
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
;   Program -->(letrec ([label (lambda () Body)]*) Body)
;   Body    -->(locals (uvar*) (new-frames (Frame*) Tail))
;   Frame   --> (uvar*)
;   Tail    -->(Triv Loc*)
;            |(if Pred Tail Tail)
;            |(begin Effect* Tail)
;   Pred    -->(true)
;            |(false)
;            |(relop Triv Triv)
;            |(if Pred Pred Pred)
;            |(begin Effect* Pred)
;   Effect-->(nop)
;            |(set! Var Triv)
;            |(set! Var (binop Triv Triv))
;            |(set! Var (alloc Triv))
;            |(set! Var (mref Triv Triv))
;            |(mset! Triv Triv Triv)
;            |(return-point label Tail)
;            |(if Pred Effect Effect)
;            |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv   -->Var | int | label
;
; Output Language:  
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body   -->(locals (uvar*) (new-frames (Frame*) Tail))
;   Frame  --> (uvar*)
;   Tail   -->(Triv Loc*)
;            |(if Pred Tail Tail)
;            |(begin Effect* Tail)
;   Pred   -->(true)
;            |(false)
;            |(relop Triv Triv)
;            |(if Pred Pred Pred)
;            |(begin Effect* Pred)
;   Effect-->(nop)
;            |(set! Var Triv)
;            |(set! Var (binop Triv Triv))
;            |(set! Var (mref Triv Triv))
;            |(mset! Triv Triv Triv)
;            |(return-point label Tail)
;            |(if Pred Effect Effect)
;            |(begin Effect* Effect)
;   Loc    -->reg  | fvar
;   Var    -->uvar | Loc
;   Triv   -->Var | int | label
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
;   variables and frame locations. Spills contain only
;   the call-live variables. The call-live form contains
;   both spills and frame locations that are live across
;   non tail calls.
;
; Input Language:  
;   Program -->(letrec ([label (lambda () Body)]*) Body)
;   Body    -->(locals (uvar*) (new-frames (Frame*) Tail))
;   Frame   -->(uvar*)
;   Tail    -->(Triv Loc*)
;            | (if Pred Tail Tail)
;            | (begin Effect* Tail)
;   Pred    -->(true)
;            | (false)
;            | (relop Triv Triv)
;            | (if Pred Pred Pred)
;            | (begin Effect* Pred)
;   Effect  -->(nop)
;            | (set! Var Triv)
;            | (set! Var (binop Triv Triv))
;            | (set! Var (mref Triv Triv))
;            | (mset! Triv Triv Triv)
;            | (return-point label Tail)
;            | (if Pred Effect Effect)
;            | (begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv   -->Var | int | label
;
; Output Language: 
;   Note. Only Body form is changed.
;
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body   -->(locals (uvar*)
;              (new-frames (Frame*)
;                (spills (uvar*)
;                  (frame-conflict conflict-graph 
;                    (call-live (uvar/fvar*) Tail)))))
;   Frame   --> (uvar*)
;   Tail    -->(Triv Loc*)
;            | (if Pred Tail Tail)
;            | (begin Effect* Tail)
;   Pred    -->(true)
;            | (false)
;            | (relop Triv Triv)
;            | (if Pred Pred Pred)
;            | (begin Effect* Pred)
;   Effect  -->(nop)
;            | (set! Var Triv)
;            | (set! Var (binop Triv Triv))
;            | (set! Var (mref Triv Triv))
;            | (mset! Triv Triv Triv)
;            | (return-point label Tail)
;            | (if Pred Effect Effect)
;            | (begin Effect* Effect)
;   Loc     -->reg | fvar
;   Var     -->uvar | Loc
;   Triv    -->Var | int | label
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
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                (new-frames (Frame*)
;                  (spills (uvar*)
;                    (frame-conflict conflict-graph 
;                      (call-live (uvar/fvar*) Tail)))))
;   Frame   --> (uvar*)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
;
; Output Language: 
;   Note. Only Body form is changed.

;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                (new-frames (Frame*)
;                  (locate ([uvar fvar]*)
;                    (frame-conflict conflict-graph 
;                      (call-live (uvar/fvar*) Tail)))))
;   Frame   --> (uvar*)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
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
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                (new-frames (Frame*)
;                  (locate ([uvar fvar]*)
;                    (frame-conflict conflict-graph 
;                      (call-live (uvar/fvar*) Tail)))))
;   Frame   --> (uvar*)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
;
; Output Language: 
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                (ulocals ()
;                  (locate ([uvar fvar]*)
;                    (frame-conflict conflict-graph Tail))))
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
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
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                 (ulocals (uvar*)
;                   (locate ([uvar fvar]*)
;                     (frame-conflict conflict-graph Tail))))
;            |  (locate ([uvar fvar]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
;
; Output Language:
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                 (ulocals (uvar*)
;                   (locate ([uvar fvar]*)
;                     (frame-conflict conflict-graph Tail))))
;            |  (locate ([uvar fvar]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
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
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                 (ulocals (uvar*)
;                   (locate ([uvar fvar]*)
;                     (frame-conflict conflict-graph Tail))))
;            |  (locate ([uvar fvar]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
;
; Output:
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;                 (ulocals (uvar*)
;                   (locate ([uvar fvar]*)
;                     (frame-conflict conflict-graph Tail))))
;            |  (locate ([uvar fvar]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
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
;   Program   --> (letrec ([label (lambda () Body)]*) Body)
;   Body      --> (locals (uvar*)
;                   (ulocals (uvar*)
;                     (locate ([uvar fvar]*)
;                       (frame-conflict conflict-graph Tail))))
;              |  (locate ([uvar fvar]*) Tail)
;   Tail      --> (Triv Loc*)
;              |  (if Pred Tail Tail)
;              |  (begin Effect* Tail)
;   Pred      --> (true)
;              |  (false)
;              |  (relop Triv Triv)
;              |  (if Pred Pred Pred)
;              |  (begin Effect* Pred)
;   Effect    --> (nop)
;              |  (set! Var Triv)
;              |  (set! Var (binop Triv Triv))
;              |  (set! Var (mref Triv Triv))
;              |  (mset! Triv Triv Triv)
;              |  (return-point label Tail)
;              |  (if Pred Effect Effect)
;              |  (begin Effect* Effect)
;   Loc       --> reg | fvar
;   Var       --> uvar | Loc
;   Triv      --> Var | int | label
;
; Output Language: 
;   Program   --> (letrec ([label (lambda () Body)]*) Body)
;   Body      --> (locals (uvar*)
;                   (ulocals (uvar*)
;                     (locate ([uvar fvar]*)
;                       (frame-conflict conflict-graph
;                         (register-conflict conflict-graph Tail)))))
;              |  (locate ([uvar Loc]*) Tail)
;   Tail      --> (Triv Loc*)
;              |  (if Pred Tail Tail)
;              |  (begin Effect* Tail)
;   Pred      --> (true)
;              |  (false)
;              |  (relop Triv Triv)
;              |  (if Pred Pred Pred)
;              |  (begin Effect* Pred)
;   Effect    --> (nop)
;              |  (set! Var Triv)
;              |  (set! Var (binop Triv Triv))
;              |  (set! Var (mref Triv Triv))
;              |  (mset! Triv Triv Triv)
;              |  (return-point label Tail)
;              |  (if Pred Effect Effect)
;              |  (begin Effect* Effect)
;   Loc       --> reg | fvar
;   Var       --> uvar | Loc
;   Triv      --> Var | int | label
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
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;              (ulocals (uvar*)
;            (locate ([uvar fvar]*)
;              (frame-conflict conflict-graph
;                (register-conflict conflict-graph Tail)))))
;         |  (locate ([uvar Loc]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
;
; Output Language: 
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;          (ulocals (uvar*)
;            (spills (uvar*)
;              (locate ([uvar fvar]*)
;                (frame-conflict conflict-graph Tail)))))
;         |(locate ([uvar Loc]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
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
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;          (ulocals (uvar*)
;            (spills (uvar*)
;              (locate ([uvar fvar]*)
;                (frame-conflict conflict-graph Tail)))))
;         |(locate ([uvar Loc]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
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
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;          (ulocals (uvar*)
;            (spills (uvar*)
;              (locate ([uvar fvar]*)
;                (frame-conflict conflict-graph Tail)))))
;         |(locate ([uvar Loc]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
;
; Output Language: 
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;          (ulocals (uvar*)
;            (locate ([uvar fvar]*)
;              (frame-conflict conflict-graph Tail))))
;         |  (locate ([uvar Loc]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label
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
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body    --> (locals (uvar*)
;          (ulocals (uvar*)
;            (spills (uvar*)
;              (locate ([uvar fvar]*)
;                (frame-conflict conflict-graph Tail)))))
;         |(locate ([uvar Loc]*) Tail)
;   Tail-->(Triv Loc*)
; |(if Pred Tail Tail)
; |(begin Effect* Tail)
;   Pred-->(true)
; |(false)
; |(relop Triv Triv)
; |(if Pred Pred Pred)
; |(begin Effect* Pred)
;   Effect-->(nop)
; |(set! Var Triv)
;            |  (set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |  (return-point label Tail)
; |(if Pred Effect Effect)
; |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Var    -->uvar | Loc
;   Triv    -->Var | int | label 
;
; Output Language: 
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body-->(locate ([uvar reg]*) Tail)
;   Tail-->(Triv)
;         |(if Pred Tail Tail)
;            |(begin Effect* Tail)
;   Pred-->(true)
;            |(false)
;            |(relop Triv Triv)
;         |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;   Effect-->(nop)
;         |(set! Var Triv)
;            |(set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |(return-point label Tail)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Loc   -->reg | fvar
;   Var   -->uvar | Loc
;   Triv-->Var | int | label
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
;   Program-->(letrec ([label (lambda () Body)]*) Body)
;   Body-->(locate ([uvar reg]*) Tail)
;   Tail-->(Triv)
;         |(if Pred Tail Tail)
;            |(begin Effect* Tail)
;   Pred-->(true)
;            |(false)
;            |(relop Triv Triv)
;         |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;   Effect-->(nop)
;         |(set! Var Triv)
;            |(set! Var (binop Triv Triv))
;         |(set! Var (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;            |(return-point label Tail)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Loc   -->reg | fvar
;   Var   -->uvar | Loc
;   Triv-->Var | int | label
;
; Output Language: 
;   Program-->(letrec ([label (lambda () Tail)]*) Tail)
;   Tail-->(Triv)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;         |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;   Effect-->(nop)
;         |(set! Loc Triv)
;         |(set! Loc (binop Triv Triv))
;         |(set! Loc (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;         |(return-point label Tail)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Triv-->Loc | int | label
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
;   Program-->(letrec ([label (lambda () Tail)]*) Tail)
;   Tail-->(Triv)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;            |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;   Effect-->(nop)
;         |(set! Loc Triv)
;         |(set! Loc (binop Triv Triv))
;         |(set! Loc (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;         |(return-point label Tail)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Loc    -->reg | fvar
;   Triv-->Loc | int | label 
;
; Output Language: 
;   Program-->(letrec ([label (lambda () Tail)]*) Tail)
;   Tail-->(Triv)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;            |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;   Effect-->(nop)
;         |(set! Loc Triv)
;         |(set! Loc (binop Triv Triv))
;         |(set! Loc (mref Triv Triv))
;         |(return-point label Tail)
;         |(mset! Triv Triv Triv)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Loc    -->reg | disp-opnd
;   Triv-->Loc | int | label
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
;   Program-->(letrec ([label (lambda () Tail)]*) Tail)
;   Tail-->(Triv)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;            |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;   Effect-->(nop)
;         |(set! Loc Triv)
;         |(set! Loc (binop Triv Triv))
;         |(set! Loc (mref Triv Triv))
;         |(mset! Triv Triv Triv)
;         |(return-point label Tail)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Loc    -->reg | disp-opnd
;   Triv-->Loc | int | label 
;
; Output Language: 
;   Program-->(letrec ([label (lambda () Tail)]*) Tail)
;   Tail-->(Triv)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;            |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;   Effect-->(nop)
;         |(set! Loc Triv)
;         |(set! Loc (binop Triv Triv))
;         |(return-point label Tail)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Loc    -->reg | disp-opnd | index-opnd
;   Triv-->Loc | int | label
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
;   Program-->(letrec ([label (lambda () Tail)]*) Tail)
;   Tail-->(Triv)
;         |(if Pred Tail Tail)
;         |(begin Effect* Tail)
;   Pred-->(true)
;         |(false)
;         |(relop Triv Triv)
;            |(if Pred Pred Pred)
;         |(begin Effect* Pred)
;   Effect-->(nop)
;         |(set! Loc Triv)
;         |(set! Loc (binop Triv Triv))
;         |(return-point label Tail)
;         |(if Pred Effect Effect)
;         |(begin Effect* Effect)
;   Loc    -->reg | disp-opnd | index-opnd
;   Triv-->Loc | int | label 
;
; Output Language: 
;   Program-->(letrec ([label (lambda () Tail)]*) Tail)
;   Tail-->(Triv)
;         |(if (relop Triv Triv) (,label) (,label))
;         |(begin Effect* Tail)
;   Effect  -->(set! Loc Triv)
;         |(set! Loc (binop Triv Triv))
;   Loc     -->reg | disp-opnd | index-opnd
;   Triv-->Loc | int | label
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
;   Program-->(letrec ([label (lambda () Tail)]*) Tail)
;   Tail-->(Triv)
;         |(if (relop Triv Triv) (,label) (,label))
;         |(begin Effect* Tail)
;   Effect  -->(set! Loc Triv)
;         |(set! Loc (binop Triv Triv))
;   Loc     -->reg | disp-opnd | index-opnd
;   Triv-->Loc | int | label
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
;   optimize-source
;
; Description: 
;   Performs constant-folding, copy-propagation, 
;   useless-code-elimination, and dead-code-elimination.
;
; Input Language:  
;   Program   --> Expr
;   Expr      --> label
;              |  uvar
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
;   Program  --> Expr
;   Expr      --> label
;              |  uvar
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

;---------------------------------------------------------------
; Input Language: 
;   Program  --> Expr
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
(define-who uncover-well-known
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
      [(begin ,[ex* nw**] ... ,[ex nw*])
       (values (make-begin `(,ex* ... ,ex)) 
         (remove-common `(,nw** ... ... ,nw* ...)))]
      [(if ,[pred pnw*] ,[conseq cnw*] ,[alter anw*])
       (values `(if ,pred ,conseq ,alter) 
         (remove-common `(,pnw* ... ,cnw* ... ,anw* ...)))]
      [(quote ,imm) (values `(quote ,imm) '())]
      [(let ([,uvar* ,[ex* nw**]] ...) ,[ex nw*])
       (values `(let ([,uvar* ,ex*] ...) ,ex)
         (remove-common `(,nw** ... ... ,nw* ...)))]
      [(letrec ([,label* (lambda (,fml** ...) 
                           (bind-free (,uvar** ...) ,[ex* nw**]))] ...)
         (closures ([,cp* ,lb* ,f** ...] ...) ,[ex nw*]))
       (let ([nw* (remove-common `(,nw** ... ... ,nw* ...))])
         (let ([wk* (difference cp* nw*)])
           (values `(letrec ([,label* (lambda (,fml** ...)
                                        (bind-free (,uvar** ...) ,ex*))] ...)
                      (closures ([,cp* ,lb* ,f** ...] ...)
                        (well-known ,wk* ,ex)))
             (difference nw* cp*))))]
      [,uvar (guard (uvar? uvar)) (values uvar `(,uvar))]
      [,label (guard (label? label)) (values label '())]
      [(,prim ,[ex* nw**] ...) (guard (memq prim primitives))
       (values `(,prim ,ex* ...) (remove-common `(,nw** ... ...)))]
      [(,label ,cp ,[rand* nw**] ...) (guard (label? label) (uvar? cp))
       (values `(,label ,cp ,rand* ...) (remove-common `(,nw** ... ...)))]
      [(,[rator nw*] ,[rand* nw**] ...)
       (values `(,rator ,rand* ...) (remove-common `(,nw* ... ,nw** ... ...)))]
      [,x (error who "invalid Expr ~s" x)]))
  (lambda (x)
    (match x
      [,[Expr -> ex nw*] ex])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Input Language: 
;   Program  --> Expr
;   Expr      --> label
;              |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([label (lambda (uvar*) 
;                                   (bind-free (uvar*) Expr))]*)
;                   (closures ([uvar label uvar*]*)
;                     (well-known (uvar*) Expr)))
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
(define-who optimize-free
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                         < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                         set-car! set-cdr! vector-set!))
  (define remove-common
    (lambda (s)
      (cond
        [(null? s) '()]
        [else (cons (car s) (remove-common (remq (car s) (cdr s))))])))
  
  (define-record node (name free*) ([wkmt #t] [link* '()]))
  
  ;; cfree** is the list of free variables of each closure in closures form
  (define (prune-free name* cfree** wk* wkmt*)
    ;; free** is the list of "known to be free" variables
    (let ([free** (map (let ([x* (remove-common `(,@wkmt* ,@name*))])
                         (lambda (free*) (difference free* x*))) cfree**)])
      ;; nbnd* is a set of node bindings of the (name . node) form
      (let ([nbnd* (map (lambda (name free*) 
                          `(,name . ,(make-node name free*))) name* free**)])
        ;; add links
        (for-each
          (lambda (nbnd cfree*)
            (for-each
              (lambda (cfree)
                (let ([nb (assq cfree nbnd*)])
                  (if nb
                      (set-node-link*! (cdr nb)
                        (cons (cdr nbnd) (node-link* (cdr nb)))))))
              cfree*))
          nbnd* cfree**)
        
        ;; Process each record and propage info to other nodes
        (for-each 
          (letrec ([f (lambda (nbnd)
                        (if (node-wkmt (cdr nbnd))
                            (if (or (not (memq (car nbnd) wk*))
                                    (not (null? (node-free* (cdr nbnd)))))
                                (begin
                                  (set-node-wkmt! (cdr nbnd) #f)
                                  (for-each
                                    (lambda (node)
                                      (set-node-free*! node (cons (car nbnd) (node-free* node)))
                                      (f (assq (node-name node) nbnd*)))
                                    (node-link* (cdr nbnd)))))))]) 
            f)
          nbnd*)
        
        ;; Extract info on final free** and wkmt*
        (let ([free** (map (lambda (nbnd) (node-free* (cdr nbnd))) nbnd*)])
          (let loop ([nbnd* nbnd*] [wkmt* wkmt*])
            (if (null? nbnd*)
                (values free** wkmt*)
                (if (node-wkmt (cdar nbnd*))
                    (loop (cdr nbnd*) (cons (caar nbnd*) wkmt*))
                    (loop (cdr nbnd*) wkmt*))))))))
    
  (define (Expr wkmt*)
    (lambda (ex)
      (match ex
        [(begin ,[ex*] ... ,[ex])
         (make-begin `(,ex* ... ,ex))]
        [(if ,[pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(quote ,imm) `(quote ,imm)]
        [(let ([,uvar* ,[ex*]] ...) ,[ex])
         `(let ([,uvar* ,ex*] ...) ,ex)]
        [,uvar (guard (uvar? uvar)) uvar]
        ;; The order of letrec bindings and closures are assumed to be the same
        [(letrec ([,lb* (lambda (,cp* ,fml** ...) (bind-free (,cp* ,free** ...) ,ex*))] ...)
           (closures ([,name* ,lb* ,free** ...] ...)
             (well-known (,wk* ...) ,ex)))
         ;; free** in LHS will be the new list of lists with free variables for each closure  
        (let-values ([(free** wkmt*) (prune-free name* free** wk* wkmt*)])
          ;; cs* is the filtered set of closures, which doesn't have wkmt closures
          ;; wkmtlb* is the list of labels for wkmt closures
          (let (
                [cs* (filter (lambda (cs) (not (memq (car cs) wkmt*)))
                             `((,name* ,lb* ,free** ...) ...))]
                [wkmtlb* (map cdr (filter (lambda (bnd) (memq (car bnd) wkmt*))
                                          `((,name* . ,lb*) ...)))]
                [ex* (map (Expr wkmt*) ex*)]
                [ex ((Expr wkmt*) ex)])
            ;; bnd* is the list of new letrec bindings
            (let ([bnd* (map (lambda (lb cp fml* free* ex)
                               (if (memq lb wkmtlb*)
                                   `(,lb (lambda (,fml* ...) (bind-free (dummy) ,ex)))
                                   `(,lb (lambda (,cp ,fml* ...) (bind-free (,cp ,free* ...) ,ex)))))
                             lb* cp* fml** free** ex*)])
              `(letrec ,bnd* (closures ,cs* ,ex)))))]
        [,label (guard (label? label)) label]
        [(,prim ,[ex*] ...) (guard (memq prim primitives)) `(,prim ,ex* ...)]
        ;; Handle direct calls separately to remove possible well-known empty case.
        ;; If the name is of a well-known empty closure then this will remove it.
        [(,label ,name ,[rand*] ...) (guard (label? label) (uvar? name))
         (if (memq name wkmt*) `(,label ,rand* ...) `(,label ,name ,rand* ...))]
        [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (match x
      [,[(Expr '()) -> ex] ex]))) 
;---------------------------------------------------------------

  
;---------------------------------------------------------------
; Input Language: 
;   Program  --> Expr
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
(define-who optimize-self-reference
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                         < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                         set-car! set-cdr! vector-set!))
  (define (Lambda name-cp* name)
    (lambda (lamb)
      (match lamb
        [(lambda (,fml* ...) (bind-free (,cp ,[(Expr name-cp*) -> f*] ...) ,ex))
         (let ([ex (if name 
                       ((Expr (cons `(,name . ,cp) name-cp*)) ex)
                       ((Expr name-cp*) ex))])
           `(lambda (,fml* ...) 
              (bind-free (,cp ,(if name (remq name f*) f*) ...) ,ex)))]
        [,x (error who "invalid Lambda ~s" x)])))
  (define (Expr name-cp*)
    (lambda (ex)
      (match ex
        [(begin ,[ex*] ... ,[ex])
         (make-begin `(,ex* ... ,ex))]
        [(if ,[pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(quote ,imm) `(quote ,imm)]
        [(let ([,uvar* ,[ex*]] ...) ,[ex])
         `(let ([,uvar* ,ex*] ...) ,ex)]
        [(letrec ([,label* ,lamb*] ...)            
           (closures ([,name* ,lb* ,[f**] ...] ...) ,[ex]))
         (let ([bnd* `((,lb* . (,name* ,f** ...)) ...)])
           (let ([lamb* (map 
                         (lambda (label lamb)
                           (let ([bnd (assq label bnd*)])
                             (if bnd
                                 (if (memq (cadr bnd) (cddr bnd))
                                     ((Lambda name-cp* (cadr bnd)) lamb)
                                     ((Lambda name-cp* #f) lamb))
                                 ((Lambda name-cp* #f) lamb))))
                         label* lamb*)])
             `(letrec ([,label* ,lamb*] ...)
                (closures ([,name* ,lb* ,(map remq name* f**) ...] ...) ,ex))))]
        [,uvar (guard (uvar? uvar))
          (if (not (null? name-cp*))
              (let ([name-cp (assq uvar name-cp*)])
                (if name-cp (cdr name-cp) uvar))
              uvar)]
        [,label (guard (label? label)) label]
        [(,prim ,[ex*] ...) (guard (memq prim primitives))
         `(,prim ,ex* ...)]
        [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (match x
      [,[(Expr '()) -> ex] ex])))
;--------------------------------------------------------------- 


;--------------------------------------------------------------- 
; Borrowed from the assignment description itself
(define-who analyze-closure-size
  (define primitives
    '(+ - * <= < = >= > boolean? car cdr cons eq? fixnum?
      make-vector null? pair? procedure? set-car! set-cdr! vector?
      vector-length vector-ref vector-set! void))
  (define Lambda
    (lambda (x)
      (match x
        [(lambda (,fml* ...)
           (bind-free (,cp ,free* ...)
             ,[Expr -> s*]))
         s*]
        [,x (error who "invalid Lambda ~s" x)])))
  (define Expr
    (lambda (x)
      (match x
        [,label (guard (label? label)) '()]
        [,uvar (guard (uvar? uvar)) '()]
        [(quote ,imm) '()]
        [(if ,[test-s*] ,[conseq-s*] ,[altern-s*])
         (append test-s* conseq-s* altern-s*)]
        [(begin ,[s**] ... ,[s*]) (apply append s* s**)]
        [(let ([,lhs* ,[s**]] ...) ,[s*]) (apply append s* s**)]
        [(letrec ([,llabel* ,[Lambda -> s**]] ...)
           (closures ([,name* ,clabel* ,free** ...] ...)
             ,[s*]))
         (apply append (map length free**) s* s**)]
        [(,prim ,[s**] ...)
         (guard (memq prim primitives))
         (apply append s**)]
        [(,[s*] ,[s**] ...) (apply append s* s**)]
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (let ([s* (Expr x)])
      (let ([n (length s*)])
        (printf "num = ~s, avg = ~s: ~s\n"
          n
          (if (= n 0) '* (exact->inexact (/ (apply + s*) n)))
          s*)))
    x))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Compiler passes
;---------------------------------------------------------------
(compiler-passes '(
  parse-scheme
  convert-complex-datum
  uncover-assigned
  purify-letrec
  convert-assignments
optimize-direct-call
  remove-anonymous-lambda
  sanitize-binding-forms
  uncover-free
  convert-closures
  analyze-closure-size
optimize-known-call
uncover-well-known
optimize-free
optimize-self-reference
  analyze-closure-size
  introduce-procedure-primitives
optimize-source
  lift-letrec
  normalize-context
  verify-a11-output
  specify-representation
  verify-a10-output
  uncover-locals
  remove-let
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
optimize-jumps
  flatten-program
  generate-x86-64
))
;---------------------------------------------------------------