; Saliya Ekanayake
; sekanaya
; Assignment 1



(define binop '(+ - *))
(define asmops '((+ . addq) (- . subq) (* . imulq)))

;--------------------------------------------------------------------------------
; Pass:            verify-scheme
;
; Description:     This pass will check the input string (program) against
;                  the input language. If the program conforms to it, then
;                  it will output a string equal to the input string. If the
;                  program is erroneous w.r.t. the input language then an
;                  appropriate error message is returned.
;
; Input Language:  Program	-->	(begin Statement+)
;                  Statement-->	(set! Var1 int64)
;                            |	(set! Var1 Var2)
;                            |	(set! Var1 (Binop Var1 int32))
;                            |	(set! Var1 (Binop Var1 Var2))
;                  Var    	-->	rax | rcx | rdx | rbx | rbp | rsi | rdi
;                            |	r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
;                  Binop 	-->	+ | - | *
;
; Output Language: Same as Input Language
;--------------------------------------------------------------------------------
(define verify-scheme
  (lambda (s)
    (define Program
      (lambda (s)
        (match s
          [(begin ,[Statement -> stmnt] ,[Statement -> stmnt*] ...)
           `(begin ,stmnt ,stmnt* ...)]
          [,other (error 'verify-scheme "invalid Program ~s" other)])))
    (define Statement
      (lambda (s)
        (match s
          [(set! ,var1 (,[Binop -> bop] ,var2 ,x))           
           (guard (and (int32? x) (eq? var1 var2) (register? var1)))
           `(set! ,var1 (,bop ,var2 ,x))]
          [(set! ,var1 (,[Binop -> bop] ,var2 ,var3))
           (guard (and (eq? var1 var2) (for-all register? `(,var1 ,var3))))
           `(set! ,var1 (,bop ,var2 ,var3))]
          [(set! ,var1 ,x) (guard (int64? x) (register? var1))
           `(set! ,var1 ,x)]          
          [(set! ,var1 ,var2) (guard (for-all register? `(,var1 ,var2))) 
           `(set! ,var1 ,var2)]
          [,other (error 'verify-scheme "invalid Statement ~s" other)])))  
    (define Binop
      (lambda (s)
        (if (memq s binop)
            s
            (error 'verify-scheme "invalid Binop ~s" s))))
    (Program s)))


;--------------------------------------------------------------------------------
; Pass:            generate-x86-64
;
; Description:     This pass will generate x86_64 assembly instructions for the 
;                  given program of the input language. It relies on the verification
;                  of the program by an earlier pass (in this case verify-scheme pass).
;                  It uses several helper methods to generate the assembly code
;                  wrapped around necessary code to use with runtime.c.
;
; Input Language:  Program	-->	(begin Statement+)
;                  Statement-->	(set! Var1 int64)
;                            |	(set! Var1 Var2)
;                            |	(set! Var1 (Binop Var1 int32))
;                            |	(set! Var1 (Binop Var1 Var2))
;                  Var    	-->	rax | rcx | rdx | rbx | rbp | rsi | rdi
;                            |	r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
;                  Binop 	-->	+ | - | *
;
; Output Language: x86_64 assembly
;--------------------------------------------------------------------------------
(define generate-x86-64
  (lambda (s)
    (define Program
      (lambda (s)
        (match s
          [(begin ,stmnt ,stmnt* ...)
           ; This is a macro expansion. So applications happen after expansion
           (emit-program (Statement stmnt) (for-each Statement stmnt*))
           ])))
    (define Statement
      (lambda (s)
        (match s
          [(set! ,var1 (,[Binop -> bop] ,var2 ,x))           
           (guard (and (int32? x) (eq? var1 var2) (register? var1)))
           (emit bop x var1)]
          [(set! ,var1 (,[Binop -> bop] ,var2 ,var3))
           (guard (and (eq? var1 var2) (for-all register? `(,var1 ,var3))))
           (emit bop var3 var1)]
          [(set! ,var1 ,x) (guard (and (register? var1) (or (int64? x) (register? x))))
           (emit 'movq x var1)])))  
    (define Binop
      (lambda (s)
        (cdr (assq s asmops))))
    (Program s)))