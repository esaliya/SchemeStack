; Saliya Ekanayake
; sekanaya
; Assignment 10

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
;   Program	-->	(letrec ([label (lambda (uvar*) Value)]*) Value)
;   Value	-->	label
;            |	uvar
;            |	(quote Immediate)
;            |	(if Pred Value Value)
;            |	(begin Effect* Value)
;            |	(let ([uvar Value]*) Value)
;            |	(value-prim Value*)
;            |	(Value Value*)
;   Pred	-->	(true)
;            |	(false)
;            |	(if Pred Pred Pred)
;            |	(begin Effect* Pred)
;            |	(let ([uvar Value]*) Pred)
;            |	(pred-prim Value*)
;   Effect	-->	(nop)
;            |	(if Pred Effect Effect)
;            |	(begin Effect* Effect)
;            |	(let ([uvar Value]*) Effect)
;            |	(effect-prim Value*)
;            |	(Value Value*)
;   Immediate	-->	fixnum | () | #t | #f
;
;   value-prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length,
;     vector-ref, void
;
;   pred-prim:
;     <, <=, =, >=, >, boolean?, eq?, fixnum?, null?, pair?, vector?
;
;   effect-prim:
;     set-car!, set-cdr!, vector-set!
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda (uvar*) Tail)]*) Tail)
;   Tail	-->	Triv
;	         |	(alloc Value)
;	         |	(binop Value Value)
;	         |	(Value Value*)
;	         |	(if Pred Tail Tail)
;	         |	(begin Effect* Tail)
;            |  (let ([uvar Value]*) Tail)
;   Pred	-->	(true)
;	         |	(false)
;	         |	(relop Value Value)
;            |	(if Pred Pred Pred)
;	         |	(begin Effect* Pred)
;            |  (let ([uvar Value]*) Pred)
;  Effect	-->	(nop)
;	         |	(mset! Value Value Value)
;            |  (Value Value*)
;	         |	(if Pred Effect Effect)
;	         |	(begin Effect* Effect)
;            |  (let ([uvar Value]*) Effect)
;  Value	-->	Triv
;	         |	(alloc Value)
;	         |	(binop Value Value)
;            |  (Value Value*)
;	         |	(if Pred Value Value)
;	         |	(begin Effect* Value)
;            |  (let ([uvar Value]*) Value)
;   Triv	-->	uvar | int | label 
;---------------------------------------------------------------
(define-who specify-representation
  (define value-prim '(+ - * car cdr cons make-vector vector-length vector-ref void))
  (define pred-prim '(< <= = >= > boolean? eq? fixnum? null? pair? vector?))
  (define effect-prim '(set-car! set-cdr! vector-set!))

  (define imm-op '(+ - * < <= = >= > void))
  (define non-imm-op '(car cdr cons make-vector vector-length vector-ref set-car! set-cdr! vector-set!))
  (define pred-op '(boolean? fixnum? null? pair? vector? eq?))
  
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
                       ,tmp2))))))]))
  (define (handle-pred-op x)
    (match x
      [(boolean? ,e) `(= (logand ,e ,mask-boolean) ,tag-boolean)]
      [(fixnum? ,e) `(= (logand ,e ,mask-fixnum) ,tag-fixnum)]
      [(pair? ,e) `(= (logand ,e ,mask-pair) ,tag-pair)]
      [(vector? ,e) `(= (logand ,e ,mask-vector) ,tag-vector)]
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