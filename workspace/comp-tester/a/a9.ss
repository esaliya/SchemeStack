; Saliya Ekanayake
; sekanaya
; Assignment 9
   
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
;   Body   --> (locals (uvar*) Tail)
;   Tail   --> Triv
;           | (alloc Value)
;           | (binop Value Value)
;           | (Value Value*)
;           | (if Pred Tail Tail)
;           | (begin Effect* Tail)
;           | (let ([uvar Value]*) Tail)
;   Pred   -->(true)
;           | (false)
;           | (relop Value Value)
;           | (if Pred Pred Pred)
;           | (begin Effect* Pred)
;           | (let ([uvar Value]*) Pred)
;  Effect  -->(nop)
;           | (mset! Value Value Value)
;           | (Value Value*)
;           | (if Pred Effect Effect)
;           | (begin Effect* Effect)
;           | (let ([uvar Value]*) Effect)
;  Value   --> Triv
;           | (alloc Value)
;           | (binop Value Value)
;           | (Value Value*)
;           | (if Pred Value Value)
;           | (begin Effect* Value)
;           | (let ([uvar Value]*) Value)
;   Triv   --> uvar | int | label 
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
;            | (if Pred Pred Pred)
;          | (begin Effect* Pred)
;  Effect --> (nop)
;          | (set! uvar Value)
;          | (mset! Value Value Value)
;            |  (Value Value*)
;          | (if Pred Effect Effect)
;          | (begin Effect* Effect)
;  Value --> Triv
;          | (alloc Value)
;          | (mref Value Value)
;          | (binop Value Value)
;            |  (Value Value*)
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