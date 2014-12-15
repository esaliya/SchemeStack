; Main for ac with a12 work
; Added optimize-known-call pass in the main along with analyze-closure-size
(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "uil.ss")

(load "a9.ss")       ; for uncover-locals and remove-let

(load "a12-rest.ss") ; for verify-a11-output and verify-a10-output, and optimize-jumps

(load "a12.ss")      ; for uncover-free convert-closures introduce-procedure-primitives,
                     ;     lift-letrec, normalize-context, and specify-representation     

(load "ab.ss")       ; for optimize-source
(load "ac.ss")       ; for uncover-well-know, optimize-free, and optimize-self-reference

(load "a12-verify.ss")

(load "../a12-wrapper.ss")   ; defines syntactic forms and procedures
                             ; needed to output of each pass

;---------------------------------------------------------------
; Compiler passes
;---------------------------------------------------------------
(compiler-passes '(
  verify-scheme 
  uncover-free
  convert-closures
;;  analyze-closure-size
optimize-known-call
uncover-well-known
optimize-free
optimize-self-reference
;;  analyze-closure-size
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

(load "../tests12.ss")

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


;---------------------------------------------------------------  
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