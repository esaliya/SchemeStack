;;; Andy Keep, Kent Dybvig
;;; P423/P523
;;; Spring 2010

;;;  verify-scheme accepts a signle value and verifies that the value
;;;  is a valid program in the current source language.
;;;
;;;  Grammar for verify-scheme (assignment 6):
;;;
;;;  Program --> (letrec ([<label> (lambda (<uvar>*) <Body>)]*) <Body>)
;;;  Body    --> (locals (<uvar>*) <Tail>)
;;;  Tail    --> <Triv>
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
;;;           |  (set! <uvar> <Value>)
;;;           |  (if <Pred> <Effect> <Effect>)
;;;           |  (begin <Effect>* <Effect>)
;;;  Value   --> <Triv>
;;;           |  (<binop> <Value> <Value>)
;;;           |  (if <Pred> <Value> <Value>)
;;;           |  (begin <Effect>* <Value>)
;;;  Triv    --> <uvar> | <int64> | <label>
;;;  
;;;  Where uvar is symbol.n where (n >= 0)
;;;        label is symbol$n where (n >= 0)
;;;        binop is +, -, *, logand, logor, or sra
;;;        relop is <, >, <=, >=, =
;;;
;;;  We still have a couple constraints based on our machine and
;;;  testing framework. Namely, we expect calls target values to
;;;  evaluate to uvars or labels, and we expect computations to be 
;;;  done with uvars or integers.
;;;
;;;  Note that we also expect the sra binop to have a uint6 in the
;;;  second argument.
;;;

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
        t)))
  (define Value
    (lambda (label* uvar*)
      (lambda (val)
        (match val
          [(if ,[(Pred label* uvar*) -> test] ,[conseq] ,[altern]) (void)]
          [(begin ,[(Effect label* uvar*) -> ef*] ... ,[val]) (void)]
          [(sra ,[x] ,y)
           (unless (uint6? y)
             (error who "invalid sra operand ~s" y))]
          [(,binop ,[x] ,[y])
           (guard (memq binop '(+ - * logand logor sra)))
           (void)]
          [,[(Triv label* uvar*) -> tr] (void)]))))
  (define Effect
    (lambda (label* uvar*)
      (lambda (ef)
        (match ef
          [(nop) (void)]
          [(if ,[(Pred label* uvar*) -> test] ,[conseq] ,[altern]) (void)]
          [(begin ,[ef*] ... ,[ef]) (void)]
          [(set! ,var ,[(Value label* uvar*) -> val])
           (unless (memq var uvar*)
             (error who "assignment to unbound var ~s" var))]
          [,ef (error who "invalid Effect ~s" ef)]))))
  (define Pred
    (lambda (label* uvar*)
      (lambda (pr)
        (match pr
          [(true) (void)]
          [(false) (void)]
          [(if ,[test] ,[conseq] ,[altern]) (void)]
          [(begin ,[(Effect label* uvar*) -> ef*] ... ,[pr]) (void)]
          [(,relop ,[(Value label* uvar*) -> x] ,[(Value label* uvar*) -> y])
           (unless (memq relop '(< > <= >= =))
             (error who "invalid predicate operator ~s" relop))]
          [,pr (error who "invalid Pred ~s" pr)]))))
  (define Tail
    (lambda (tail label* uvar*)
      (match tail
        [(if ,[(Pred label* uvar*) -> test] ,[conseq] ,[altern]) (void)]
        [(begin ,[(Effect label* uvar*) -> ef*] ... ,[tail]) (void)]
        [(sra ,[(Value label* uvar*) -> x] ,y)
         (unless (uint6? y)
           (error who "invalid sra operand ~s" y))]
        [(,binop ,[(Value label* uvar*) -> x] ,[(Value label* uvar*) -> y])
         (guard (memq binop '(+ - * logand logor sra)))
         (void)]
        [(,[(Value label* uvar*) -> rator] 
           ,[(Value label* uvar*) -> rand*] ...)
         (void)]
        [,[(Triv label* uvar*) -> triv] (void)])))
  (define Body
    (lambda (label*)
      (lambda (bd fml*)
        (match bd
          [(locals (,local* ...) ,tail)
           (let ([uvar* `(,fml* ... ,local* ...)])
             (verify-x-list uvar* uvar? 'uvar)
             (Tail tail label* uvar*))]
          [,bd (error who "invalid Body ~s" bd)]))))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)
       (verify-x-list label* label? 'label)
       (map (lambda (fml*) (verify-x-list fml* uvar? 'formal)) fml**)
       (for-each (Body label*) bd* fml**)
       ((Body label*) bd '())]
      [,x (error who "invalid Program ~s" x)])
    x))

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
          (memq x '(+ - * logand logor sra)) (memq x '(= < <= > >=))))
    (define (triv? x) (or (uvar? x) (int64? x) (label? x)))
    (define (Value val)
      (match val
        [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[val]) (make-begin `(,ef* ... ,val))]
        [(,binop ,x ,y)
         (guard (memq binop '(+ - * logand logor sra)))
         (trivialize-call `(,binop ,x ,y))]
        [,tr (guard (triv? tr)) tr]
        [,val (error who "invalid Value ~s" val)]))
    (define (Effect ef)
      (match ef
        [(nop) '(nop)]
        [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
        [(set! ,var ,[Value -> val]) `(set! ,var ,val)]
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

(define-who flatten-set!
  (define (trivialize-set! lhs rhs)
    (match rhs
      [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
      [(begin ,[Effect -> ef*] ... ,[rhs]) (make-begin `(,ef* ... ,rhs))]
      [(,binop ,[Triv -> x] ,[Triv -> y]) 
       (guard (memq binop '(+ - * logand logor sra)))
       `(set! ,lhs (,binop ,x ,y))]
      [,tr (guard (triv? tr)) `(set! ,lhs ,tr)]
      [,rhs (error who "invalid set! Rhs ~s" rhs)]))
  (define (triv? x) (or (uvar? x) (int64? x) (label? x)))
  (define (Triv t) (if (triv? t) t (error who "invalid Triv ~s" t)))
  (define (Effect ef)
    (match ef
      [(nop) '(nop)]
      [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
      [(begin ,[Effect -> ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
      [(set! ,var ,val) (trivialize-set! var val)]
      [,ef (error who "invalid Effect ~s" ef)]))
  (define (Pred pr) ---)
  (define (Tail tail) ---)
  (define (Body bd)
    (match bd
      [(locals (,uvar* ...) ,[Tail -> tail]) `(locals (,uvar* ...) ,tail)]
      [,bd (error who "invalid Body ~s" bd)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,[Body -> bd*])] ...)
         ,[Body -> bd])
       `(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)]
      [,x (error who "invalid Program ~s" x)])))

(define-who impose-calling-conventions
  (define (argument-locations args)
    (let f ([args args] [regs parameter-registers] [fv-idx 0])
      (cond
        [(null? args) '()]
        [(null? regs) 
         (cons (index->frame-var fv-idx) (f (cdr args) regs (+ fv-idx 1)))]
        [else (cons (car regs) (f (cdr args) (cdr regs) fv-idx))])))
  (define (triv? x) (or (uvar? x) (int64? x) (label? x)))
  (define (Triv t) (if (triv? t) t (error who "invalid Triv ~s" t)))
  (define (Effect ef)
    (match ef
      [(nop) '(nop)]
      [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
      [(begin ,[ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
      [(set! ,var (,binop ,[Triv -> x] ,[Triv -> y]))
       `(set! ,var (,binop ,x ,y))]
      [(set! ,var ,[Triv -> tr]) `(set! ,var ,tr)]
      [,ef (error who "invalid Effect ~s" ef)]))
  (define (Pred pr) ---)
  (define (Tail tail rp)
    (match tail
      [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
      [(begin ,[Effect -> ef*] ... ,[tail]) (make-begin `(,ef* ... ,tail))]
      [(,binop ,[Triv -> x] ,[Triv -> y])
       (guard (memq binop '(+ - * logand logor sra)))
       ---]
      [(,[Triv -> rator] ,[Triv -> rand*] ...)
       (let ([loc* (argument-locations rand*)])
         ---)]
      [,tr (guard (triv? tr)) ---]
      [,tail (error who "invalid Tail ~s" tail)]))
  (define (Body bd fml*)
    (match bd
      [(locals (,local* ...) ,tail)
       (let ([rp (unique-name 'rp)] [fml-loc* (argument-locations fml*)])
         (let ([tail (Tail tail rp)])
           `(locals (,rp ,fml* ... ,local* ...) 
              ,(make-begin
                 `((set! ,rp ,return-address-register)
                   (set! ,fml* ,fml-loc*) ...
                   ,tail)))))]
      [,bd (error who "invalid Body ~s" bd)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)
       (let ([bd* (map Body bd* fml**)] [bd (Body bd '())])
         `(letrec ([,label* (lambda () ,bd*)] ...) ,bd))]
      [,x (error who "invalid Program ~s" x)])))
