;---------------------------------------------------------------
; Pass:           
;   assign-frame
;
; Description: 
;   Assign frames for spilled variables
;
; Input Language:  
;   Same as the output of assign-registers
;
; Output Language: 
;   The only change is,
;   Body --> (locals (uvar*)
;		      (ulocals (uvar*)
;		       (locate ([uvar fvar]*)
;		        (frame-conflict conflict-graph Tail))))
;	      |  (locate ([uvar Loc]*) Tail)
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
;   assign-registers
;
; Description: 
;   Tries to assign registers for all the spillables and 
;   unspillables
;
; Input Language:  
;   Same as the output of uncover-register-conflict
;
; Output Language: 
;   The only change is,
;   Body --> (locals (uvar*)
;		      (ulocals (uvar*)
;		       (spills (uvar*)
;		        (locate ([uvar fvar]*)
;		         (frame-conflict conflict-graph Tail)))))
;	     |	(locate ([uvar Loc]*) Tail)
;---------------------------------------------------------------
(define-who assign-registers
  (define k (length registers))
  (define pick-if
    (lambda (pred? cg)
      (cond
       [(null? cg) #f]
       [(pred? (car cg)) (car cg)]
       [else (pick-if pred? (cdr cg))])))
  (define low-degree?
    (lambda (row)
      (< (sub1 (length row)) k)))
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
;   Checks if all the body elements have gone
;   through the register/frame allocator completely
;
; Input Language:  
;   Same as the out of assign-registers
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
