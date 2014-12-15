; Saliya Ekanayake
; sekanaya
; Assignment 3

;---------------------------------------------------------------
; Pass, verify-scheme is taken directly from the assignment :)
;---------------------------------------------------------------
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
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   finalize-locations
;
; Description: 
;   Relies on the output of verify-scheme pass and
;   replaces location aliases with the actual register
;   or frame variable. It also discards the locate
;   form presented in the input grammer. 
;
; Input Language:  
;   Same as the input language to verify-scheme
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
;   Loc	    -->	reg | fvar
;   Triv	-->	Loc | int | label
;---------------------------------------------------------------
(define-who finalize-locations
  (define Var->Loc
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
           `(begin ,ef* ... ,pred)]
          [(,relop ,x ,y)
           `(,relop ,(Var->Loc x env) ,(Var->Loc y env))]
          [,x (error who "invalid Pred ~s" x)]))))
  (define Effect
    (lambda (env)
      (lambda (ef)
        (match ef
          [(set! ,x (,binop ,x ,y))
           ; Var->Loc will resolve a uvar, x, to it's location. 
           ; If x is not a uvar then it's returned as it is
           (let ([x (Var->Loc x env)] [y (Var->Loc y env)])
             `(set! ,x (,binop ,x ,y)))]
          [(set! ,x ,y)
           (let ([x (Var->Loc x env)] [y (Var->Loc y env)])
             (if (eq? x y) '(nop) `(set! ,x ,y)))]
          [(if ,[(Pred env) -> pred] ,[(Effect env) -> ef1] , [(Effect env) -> ef2])
           `(if ,pred ,ef1 ,ef2)]
          [(begin ,[(Effect env) -> ef*] ... ,[(Effect env) -> ef])
           `(begin ,ef* ... ,ef)]
          [(nop) '(nop)]))))
  (define Tail
    (lambda (env)
      (lambda (tail)
        (match tail
          [(begin ,[(Effect env) -> ef*] ... ,[(Tail env) -> tail])
           `(begin ,ef* ... ,tail)]
          [(if ,[(Pred env) -> pred] ,[(Tail env) -> tail1] ,[(Tail env) -> tail2])
           `(if ,pred ,tail1 ,tail2)]
          [(,triv)
           `(,(Var->Loc triv env))]
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
          (make-disp-opnd 'rbp (ash (frame-var->index triv) 3))
          triv)))
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> pred] ,[Pred -> pred1] ,[Pred -> pred2])
         `(if ,pred ,pred1 ,pred2)]
        [(begin ,[Effect -> ef*] ... ,[Pred -> pred])
         `(begin ,ef* ... ,pred)]
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
        [(if ,[Pred -> pred] ,[Effect -> ef1] , [Effect -> ef2])
         `(if ,pred ,ef1 ,ef2)]
        [(begin ,[Effect -> ef*] ... ,[Effect -> ef])
         `(begin ,ef* ... ,ef)]
        [(nop) '(nop)])))
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
         `(begin ,ef* ... ,tail)]
        [(if ,[Pred -> pred] ,[Tail -> tail1] ,[Tail -> tail2])
         `(if ,pred ,tail1 ,tail2)]
        [(,[Triv -> triv]) `(,triv)]
        [,x (error who "invalid Tail ~s" x)])))
  (lambda (s)
    (match s
      [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
       `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)]
      [,x (error who "invalid Program ~s" x)])))
;---------------------------------------------------------------  


;---------------------------------------------------------------
; Pass:           
;   expose-basic-blocks
;
; Description: 
;   Relies on the output of expose-frame-var pass. The idea
;   of this pass is to create basic blocks for each "then",
;   "else", and "join" parts, which results due to branching
;   operation of "if". These sequential blocks are pushed to
;   to the top as thunks. In the output language branching
;   happens with conditional jumps based on the simpler form
;   of (if (relop triv triv) (clab) (flab)). All these simple
;   "if" forms appear only in the tail position of the blocks.
;
; Input Language:  
;   Same as the output language of expose-frame-var 
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Tail)]*) Tail)
;   Tail	-->	(Triv)
;	         |	(if (relop Triv Triv) (,label) (,label))
;	         |	(begin Effect* Tail)
;   Effect  -->	(set! Loc Triv)
;	         |	(set! Loc (binop Triv Triv))
;   Loc     -->	reg | disp-opnd
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

      ; no need to handle ending effect separately or 
      ; even effects before and after begin separately
      ; since we have verified the source already. So
      ; we know all these x* and ef* are just effects.
      ; In fact, handling them separately may result in
      ; nested begins, which is not in accordance with
      ; output grammar.
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
;   Same as the output language of expose-basic-blocks
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
