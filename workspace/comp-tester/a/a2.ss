; Saliya Ekanayake
; sekanaya
; Assignment 2

;---------------------------------------------------------------
; Pass, verify-scheme is taken directly from the assignment :)
;---------------------------------------------------------------
;;; Andy Keep, Kent Dybvig
;;; P423/P523
;;; Spring 2010

;;; verify-scheme accept a single value and verifies that the value
;;; is a valid program in the current source language.
;;;
;;; Grammar for the new subset:
;;;
;;; Program --> (letrec ([<label> (lambda () <Tail>)]*) <Tail>)
;;; Tail    --> (<Triv>)
;;;          |  (begin <Effect>+ <Tail>)
;;; Effect  --> (set! <Var> <Triv>)
;;;          |  (set! <Var> (<binop> <Triv> <Triv>)
;;; Var     --> reg
;;;          |  framevar        -- (fv0, fv1, fv2 ...)
;;; Triv    --> Var
;;;          |  int
;;;          |  label
;;;
;;; The code is ugly but probably inevitably so because it reflects the
;;; strange constraints of the x86_64 architecture.

(define-who verify-scheme
  (define verify-label-list
    (lambda (label*)
      (let loop ([label* label*] [idx* '()])
        (unless (null? label*)
          (let ([label (car label*)] [label* (cdr label*)])
            (unless (label? label)
              (error who "invalid label ~s found" label))
            (let ([idx (extract-suffix label)])
              (when (member idx idx*)
                (error who "non-unique label suffix ~s found" idx))
              (loop label* (cons idx idx*))))))))
  (define Var
    (lambda (var)
      (unless (or (register? var) (frame-var? var))
        (error who "invalid variable ~s" var))
      var))
  (define Triv
    (lambda (label*)
      (lambda (t)
        (unless (or (register? t) (frame-var? t) (label? t)
                    (and (integer? t) (exact? t)))
          (error who "invalid Triv ~s" t))
        (when (label? t)
          (unless (memq t label*)
            (error who "unbound label ~s" t)))
        t)))
  (define Effect
    (lambda (label*)
      (lambda (ef)
        (match ef
          [(set! ,[Var -> x] (,binop ,[(Triv label*) -> y] ,[(Triv label*) -> z]))
           (unless (and (eq? y x)
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
                          [else (error who "invalid binary operator ~s" binop)]))
             (error who "~s violates machine constraints" `(set! ,x (,binop ,y ,z))))]
          [(set! ,[Var -> x] ,[(Triv label*) -> y])
           (unless (or (and (register? x)
                            (or (register? y)
                                (frame-var? y)
                                (int64? y)
                                (label? y)))
                       (and (frame-var? x)
                            (or (register? y)
                                (int32? y))))
             (error who "~s violates machine constraints" `(set! ,x ,y)))]
          [,ef (error who "invalid Effect ~s" ef)]))))
  (define Tail
    (lambda (label*)
      (lambda (tail)
        (match tail
          [(begin ,[(Effect label*) -> ef*] ... ,tail)
           ((Tail label*) tail)]
          [(,[(Triv label*) -> t])
           (when (integer? t)
             (error who "~s violates machine constraints" `(,t)))]
          [,tail (error who "invalid Tail ~s" tail)]))))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
       (verify-label-list label*)
       (for-each (Tail label*) tail*)
       ((Tail label*) tail)]
      [,x (error who "invalid Program ~s" x)])
    x))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   expose-frame-var
;
; Description: 
;   Relies on the input from verify-scheme pass and
;   keeps everything the same except frame variables.
;   The frame variables are converted into records of
;   displacement mode operands. The rbp register is
;   the base register in computing the displacements.
;
; Input Language:  
;   Same as the input language to verify-scheme
;
; Output Language: 
;   Program --> (letrec ([<label> (lambda () <Tail>)]*) <Tail>)
;   Tail    --> (<Triv>)
;            |  (begin <Effect>+ <Tail>)
;   Effect  --> (set! <Var> <Triv>)
;            |  (set! <Var> (<binop> <Triv> <Triv>)
;   Var     --> reg
;            |  framevar  -- changed into displacement operands
;   Triv    --> Var
;            |  int
;            |  label
;---------------------------------------------------------------
(define expose-frame-var
  (lambda (s)
    (cond
     [(null? s) '()]
     [(pair? (car s)) (cons (expose-frame-var (car s)) 
                            (expose-frame-var (cdr s)))]
     [(frame-var? (car s)) 
      (cons (make-disp-opnd 'rbp (* 8 (frame-var->index (car s)))) 
            (expose-frame-var (cdr s)))]
     [else (cons (car s) (expose-frame-var (cdr s)))])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   flatten-program
;
; Description: 
;   Accepts the input from expose-frame-var and flattens
;   the program. The entire program is wrapped inside a
;   list with car equals to 'code. The Tail (body) of the
;   letrec appears next in the list. Then each of the labels,
;   followed by the body (without 'begin) of the thunk, 
;   follows. The calls of the form (Triv) are changed to 
;   (jump Triv).
;   
; Input Language:  
;   Same as the output language of expose-frame-var
;
; Output Language: 
;   (code Tail Label1 Tail1 Label2 Tail2 ...)
;   Each Tail of the original thunks are preceeded by
;   its label. See Description.
;---------------------------------------------------------------
(define-who flatten-program  
  (define Tail
    (lambda (tail)
      (match tail
        ; additional paranthesis are necessary to
        ; capture a set of set! statements.
        [(begin ,ef* ... ,[Tail -> tail])
         `(,ef* ... ,tail ...)]
        ; theoretically no need for additional (), but
        ; others expect list of list from Tail to splice
        ; out into their correct place.
        [(,t) `((jump ,t))])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
       ; tail* is something like ( tail ...)
       ; tail itself is a list of set! and calls
       (let ([p `((,label* ,tail* ...) ...)])
       `(code ,tail ... ,p ... ...))])))
;---------------------------------------------------------------


(define asmops '((+ . addq) (- . subq) (* . imulq) (logand . andq) (logor . orq) (sra . sarq)))


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
  (define Code
    (lambda (s)
      (match s
        [(set! ,x (,binop ,x ,triv)) (emit (cdr (assq binop asmops)) triv x)]
        ; if triv is a label we want to set the effective address to
        ; var rather the instruction/value referred by the address of
        ; label.
        [(set! ,var ,triv) (if (label? triv) 
                               (emit 'leaq triv var)
                               (emit 'movq triv var))]
        [(jump ,x) (emit-jump 'jmp x)]
        [,x (guard (label? x)) (emit-label x)])))
  (lambda (s)
    (match s
      [(code ,code* ...) (emit-program (for-each Code code*))])))
            

