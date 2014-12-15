;;; Andy Keep, Kent Dybvig
;;; P423/P523
;;; Spring 2010

;;; verify-scheme accept a single value and verifies that the value
;;; is a valid program in the current source language.
;;;
;;; Grammar assignment 3:
;;;
;;; Program --> (letrec ([<label> (lambda () <Body>)]*) <Body>)
;;; Body    --> (locate ([uvar <Loc>]*) <Tail>)
;;; Tail    --> (<Triv>)
;;;          |  (begin <Effect>* <Tail>)
;;;          |  (if <Pred> <Tail> <Tail>)
;;; Pred    --> (true)
;;;          |  (false)
;;;          |  (relop <Triv> <Triv>)
;;;          |  (begin <Effect>* <Pred>)
;;;          |  (if <Pred> <Pred> <Pred>)
;;; Effect  --> (nop)
;;;          |  (set! <Var> <Triv>)
;;;          |  (set! <Var> (<binop> <Triv> <Triv>)
;;;          |  (begin <Effect>+)
;;;          |  (if <Pred> <Effect> <Effect>)
;;; Var     --> uvar
;;;          |  Loc
;;; Loc     --> register
;;;          |  frame-var
;;; Triv    --> Var
;;;          |  int
;;;          |  label
;;;
;;; Where uvar is symbol.n where (n >= 0)
;;;       binop is +, -, *, logand, logor, or sra
;;;       relop is <, <=, =, >=, or >
;;;       register is rax, rcx, rdx, rbx, rbp, rdi, rsi, r8,
;;;                   r9, r10, r11, r12, r13, r14, or r15
;;;       label is symbol$n where (n >= 0)
;;;       frame-var is fvn where (n >= 0)
;;;
;;; If the value is a valid program, verify scheme returns the value
;;; unchanged; otherwise, it signals an error.

(define-who verify-scheme
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
  (define Var
    (lambda (env)
      (lambda (var)
        (unless (or (register? var) (frame-var? var) (uvar? var))
          (error who "invalid variable ~s" var))
        (when (uvar? var)
          (unless (assq var env)
            (error who "unbound uvar ~s" var)))
        var)))
  (define Loc
    (lambda (loc)
      (unless (or (register? loc) (frame-var? loc))
        (error who "invalid Loc ~s" loc))
      loc))
  (define Var->Loc
    (lambda (v env)
      (if (uvar? v) (cdr (assq v env)) v)))
  (define Triv
    (lambda (label* env)
      (lambda (t)
        (unless (or (register? t) (frame-var? t) (label? t) (uvar? t)
                    (and (integer? t) (exact? t)))
          (error who "invalid Triv ~s" t))
        (when (uvar? t)
          (unless (assq t env)
            (error who "unbound uvar ~s" t)))
        (when (label? t)
          (unless (memq t label*)
            (error who "unbound label ~s" t)))
        t)))
  (define Pred
    (lambda (label* env)
      (lambda (pr)
        (match pr
          [(true) (void)]
          [(false) (void)]
          [(begin ,[(Effect label* env) -> ef*] ... ,[pr]) (void)]
          [(if ,[test] ,[conseq] ,[altern]) (void)]
          [(,relop ,[(Triv label* env) -> x] ,[(Triv label* env) -> y])
           (unless (memq relop '(= < <= > >=))
             (error who "invalid predicate operator ~s" relop))
           (let ([x (Var->Loc x env)] [y (Var->Loc y env)])
             (unless (or (and (register? x)
                              (or (register? y)
                                  (frame-var? y)
                                  (int32? y)))
                         (and (frame-var? x)
                              (or (register? y)
                                  (int32? y))))
               (error who "~s violates machine constraints"
                      `(,relop ,x ,y))))]
          [,pr (error who "invalid Pred ~s" pr)]))))
  (define Effect
    (lambda (label* env)
      (lambda (ef)
        (match ef
          [(nop) (void)]
          [(set! ,[(Var env) -> x]
             (,binop ,[(Triv label* env) -> y] ,[(Triv label* env) -> z]))
           (unless (and (eq? y x)
                        (let ([x (Var->Loc x env)] [z (Var->Loc z env)])
                          (case binop
                            [(+ - logand logor)
                             (or (and (register? x)
                                      (or (register? z)
                                          (frame-var? z)
                                          (int32? z)))
                                 (and (frame-var? x)
                                      (or (register? z)
                                          (int32? z))))]
                            [(*)
                             (and (register? x)
                                  (or (register? z)
                                      (frame-var? z)
                                      (int32? z)))]
                            [(sra)
                             (and (or (register? x) (frame-var? x))
                                  (uint6? z))]
                            [else
                             (error who "invalid binary operator ~s" binop)])))
             (error who "~s violates machine constraints"
                    `(set! ,x (,binop ,y ,z))))]
          [(set! ,[(Var env) -> x] ,[(Triv label* env) -> y])
           (let ([x (Var->Loc x env)] [y (Var->Loc y env)])
             (unless (or (and (register? x)
                              (or (register? y)
                                  (frame-var? y)
                                  (int64? y)
                                  (label? y)))
                         (and (frame-var? x)
                              (or (register? y)
                                  (int32? y))))
               (error who "~s violates machine constraints" `(set! ,x ,y))))]
          [(begin ,[ef] ,[ef*] ...) (void)]
          [(if ,[(Pred label* env) -> test] ,[conseq] ,[altern]) (void)]
          [,ef (error who "invalid Effect ~s" ef)]))))
  (define Tail
    (lambda (label* env)
      (lambda (tail)
        (match tail
          [(begin ,[(Effect label* env) -> ef*] ... ,tail)
           ((Tail label* env) tail)]
          [(if ,[(Pred label* env) -> test] ,[conseq] ,[altern]) (void)]
          [(,[(Triv label* env) -> t])
           (when (integer? t)
             (error who "~s violates machine constraints" `(,t)))]
          [,tail (error who "invalid Tail ~s" tail)]))))
  (define Body
    (lambda (label*)
      (lambda (bd)
        (match bd
          [(locate ([,uvar* ,[Loc -> loc*]] ...) ,tail)
           (verify-x-list uvar* uvar? 'uvar)
           ((Tail label* (map cons uvar* loc*)) tail)]
          [,bd (error who "invalid Body ~s" bd)]))))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,bd*)] ...) ,bd)
       (verify-x-list label* label? 'label)
       (for-each (Body label*) bd*)
       ((Body label*) bd)]
      [,x (error who "invalid Program ~s" x)])
    x))

;;; See the assignment description for our documentation for this pass

(define-who finalize-locations
  (define Var
    (lambda (env)
      (lambda (v)
        (if (uvar? v) (cdr (assq v env)) v))))
  (define Triv
    (lambda (env)
      (lambda (t)
        (if (uvar? t) (cdr (assq t env)) t))))
  (define Pred
    (lambda (env)
      (lambda (pr)
        (match pr
          [(true) '(true)]
          [(false) '(false)]
          [(if ,[test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
          [(begin ,[(Effect env) -> ef*] ... ,[pr]) `(begin ,ef* ... ,pr)]
          [(,relop ,[(Triv env) -> x] ,[(Triv env) -> y]) `(,relop ,x ,y)]
          [,pr (error who "invalid Pred ~s" pr)]))))
  (define Effect
    (lambda (env)
      (lambda (ef)
        (match ef
          [(nop) '(nop)]
          [(set! ,[(Var env) -> x]
             (,binop ,[(Triv env) -> y] ,[(Triv env) -> z]))
           `(set! ,x (,binop ,y ,z))]
          [(set! ,[(Var env) -> x] ,[(Triv env) -> y]) 
           (if (eq? x y) '(nop) `(set! ,x ,y))]
          [(begin ,[ef] ,[ef*] ...) `(begin ,ef ,ef* ...)]
          [(if ,[(Pred env) -> test] ,[conseq] ,[altern])
           `(if ,test ,conseq ,altern)]
          [,ef (error who "invalid Effect ~s" ef)]))))
  (define Tail
    (lambda (env)
      (lambda (tail)
        (match tail
          [(begin ,[(Effect env) -> ef*] ... ,[tail]) `(begin ,ef* ... ,tail)]
          [(if ,[(Pred env) -> test] ,[conseq] ,[altern])
           `(if ,test ,conseq ,altern)]
          [(,[(Triv env) -> t]) `(,t)]
          [,tail (error who "invalid Tail ~s" tail)]))))
  (define Body
    (lambda (bd)
      (match bd
        [(locate ([,uvar* ,loc*] ...) ,[(Tail (map cons uvar* loc*)) -> tail])
         tail]
        [,bd (error who "invalid Body ~s" bd)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> bd*])] ...) ,[Body -> bd])
       `(letrec ([,label* (lambda () ,bd*)] ...) ,bd)]
      [,x (error who "invalid Program ~s" x)])))

;;; See the assignment description for our documentation for this pass

(define-who expose-frame-var
  (define Triv
    (lambda (t)
      (if (frame-var? t)
          (make-disp-opnd frame-pointer-register
            (ash (frame-var->index t) word-shift))
          t)))
  (define Pred
    (lambda (pr)
      (match pr
        [(true) '(true)]
        [(false) '(false)]
        [(if ,[test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[test])
         `(begin ,ef* ... ,test)]
        [(,relop ,[Triv -> tr1] ,[Triv -> tr2]) `(,relop ,tr1 ,tr2)]
        [,pr (error who "invalid Pred ~s" pr)])))
  (define Effect
    (lambda (st)
      (match st
        [(nop) '(nop)]
        [(set! ,[Triv -> var] (,binop ,[Triv -> t1] ,[Triv -> t2]))
         `(set! ,var (,binop ,t1 ,t2))]
        [(set! ,[Triv -> var] ,[Triv -> t])
         `(set! ,var ,t)]
        [(begin ,[ef] ,[ef*] ...) `(begin ,ef ,ef* ...)]
        [(if ,[Pred -> test] ,[conseq] ,[altern])
         `(if ,test ,conseq ,altern)]
        [,st (error who "invalid syntax for Effect ~s" st)])))
  (define Tail
    (lambda (tail)
      (match tail
        [(,[Triv -> t]) `(,t)]
        [(begin ,[Effect -> ef*] ... ,[tail])
         `(begin ,ef* ... ,tail)]
        [(if ,[Pred -> test] ,[conseq] ,[altern])
         `(if ,test ,conseq ,altern)]
        [,tail (error who "invalid syntax for Tail ~s" tail)])))
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
       `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)]
      [,program (error who "invalid syntax for Program: ~s" program)])))

;;; See the assignment description for our documentation for this pass

(define-who expose-basic-blocks
  (define (Tail x)
    (match x
      [(if ,pred ,[conseq cb*] ,[altern ab*])
       (let ([clab (unique-label 'c)] [alab (unique-label 'a)])
         (let-values ([(pred pb*) (Pred pred clab alab)])
           (values pred
             `(,pb* ...
               [,clab (lambda () ,conseq)]
               ,cb* ...
               [,alab (lambda () ,altern)]
               ,ab* ...))))]
      [(begin ,effect* ... ,[tail tb*])
       (let-values ([(x xb*) (Effect* effect* `(,tail))])
         (values x `(,xb* ... ,tb* ...)))]
      [(,triv) (values `(,triv) '())]
      [,x (error who "invalid Tail ~s" x)]))
  (define (Pred x tlab flab)
    (match x
      [(true) (values `(,tlab) '())]
      [(false) (values `(,flab) '())]
      [(if ,pred ,[conseq cb*] ,[altern ab*])
       (let ([clab (unique-label 'c)] [alab (unique-label 'a)])
         (let-values ([(pred pb*) (Pred pred clab alab)])
           (values pred
             `(,pb* ...
               [,clab (lambda () ,conseq)]
               ,cb* ...
               [,alab (lambda () ,altern)]
               ,ab* ...))))]
      [(begin ,effect* ... ,[pred pb*])
       (let-values ([(x xb*) (Effect* effect* `(,pred))])
         (values x `(,xb* ... ,pb* ...)))]
      [(,relop ,triv1 ,triv2)
       (values `(if (,relop ,triv1 ,triv2) (,tlab) (,flab)) '())]
      [,x (error who "invalid Pred ~s" x)]))
  (define (Effect* x* rest*)
    (match x*
      [() (values (make-begin rest*) '())]
      [(,x* ... ,x) (Effect x* x rest*)]))
  (define (Effect x* x rest*)
    (match x
      [(nop) (Effect* x* rest*)]
      [(set! ,lhs ,rhs) (Effect* x* `((set! ,lhs ,rhs) ,rest* ...))]
      [(if ,pred ,conseq ,altern)
       (let ([clab (unique-label 'c)]
             [alab (unique-label 'a)]
             [jlab (unique-label 'j)])
         (let-values ([(conseq cb*) (Effect '() conseq `((,jlab)))]
                      [(altern ab*) (Effect '() altern `((,jlab)))]
                      [(pred pb*) (Pred pred clab alab)])
           (let-values ([(x xb*) (Effect* x* `(,pred))])
             (values x
               `(,xb* ...
                 ,pb* ...
                 [,clab (lambda () ,conseq)]
                 ,cb* ...
                 [,alab (lambda () ,altern)]
                 ,ab* ...
                 [,jlab (lambda () ,(make-begin rest*))])))))]
      [(begin ,effect* ...) (Effect* `(,x* ... ,effect* ...) rest*)]
      [,x (error who "invalid Effect ~s" x)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Tail -> tail* b**])] ...) ,[Tail -> tail b*])
       `(letrec ([,label* (lambda () ,tail*)] ... ,b** ... ... ,b* ...) ,tail)]
      [,x (error who "invalid Program ~s" x)])))
