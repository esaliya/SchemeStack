; Saliya Ekanayake
; sekanaya
; Assignment 1


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
          [(set! ,[Var -> var1] (,[Binop -> bop] ,[Var -> var2] ,x))           
           (guard (int32? x))
           (if (eqv? var1 var2)
               `(set! ,var1 (,bop ,var2 ,x))
               (error 'verify-scheme "invalid Statement ~s" s))]
          [(set! ,[Var -> var1] (,[Binop -> bop] ,[Var -> var2] ,[Var -> var3]))
           (if (eqv? var1 var2)
               `(set! ,var1 (,bop ,var2 ,var3))
               (error 'verify-scheme "invalid Statement ~s" s))]
          [(set! ,[Var -> var1] ,x) (guard (int64? x) )
           `(set! ,var1 ,x)]          
          [(set! ,[Var -> var1] ,[Var -> var2])
           `(set! ,var1 ,var2)]
          [,other (error 'verify-scheme "invalid Statement ~s" other)])))
    (define Var
      (lambda (s)
        (match s
          [rax 'rax]
          [rcx 'rcx]
          [rdx 'rdx]
          [rbx 'rbx]
          [rbp 'rbp]
          [rsi 'rsi]
          [rdi 'rdi]
          [r8 'r8]
          [r9 'r9]
          [r10 'r10]
          [r11 'r11]
          [r12 'r12]
          [r13 'r13]
          [r14 'r14]
          [r15 'r15]
          [,other (error 'verify-scheme "invalid Var ~s" other)])))
    (define Binop
      (lambda (s)
        (match s
          [+ '+]
          [- '-]
          [* '*]
          [,other (error 'verify-scheme "invalid Binop ~s" other)])))
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
          [(set! ,[Var -> var1] (,[Binop -> bop] ,[Var -> var2] ,x))           
           (guard (int32? x))
           (if (eqv? var1 var2)
               (emit bop x var1))]
          [(set! ,[Var -> var1] (,[Binop -> bop] ,[Var -> var2] ,[Var -> var3]))
           (if (eqv? var1 var2)
               (emit bop var3 var1))]
          [(set! ,[Var -> var1] ,x) (guard (int64? x) )
           (emit 'movq x var1)]          
          [(set! ,[Var -> var1] ,[Var -> var2])
           (emit 'movq var2 var1)])))
    (define Var
      (lambda (s)
        (match s
          [rax 'rax]
          [rcx 'rcx]
          [rdx 'rdx]
          [rbx 'rbx]
          [rbp 'rbp]
          [rsi 'rsi]
          [rdi 'rdi]
          [r8 'r8]
          [r9 'r9]
          [r10 'r10]
          [r11 'r11]
          [r12 'r12]
          [r13 'r13]
          [r14 'r14]
          [r15 'r15])))
    (define Binop
      (lambda (s)
        (match s
          [+ 'addq]
          [- 'subq]
          [* 'imulq])))
    (Program s)))