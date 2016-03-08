;;; Andy Keep, Kent Dybvig
;;; P423/P523
;;; Spring 2010

;;; verify-scheme accept a single value and verifies that the value
;;; is a valid program in the current source language.
;;;
;;; Grammar for verify-scheme (assignment 4):
;;;
;;; Program --> (letrec ((<label> (lambda () <Body>))*) <Body>)
;;; Body    --> (locals (<uvar>*) <Tail>)
;;; Tail    --> (<Triv> <Var>*)
;;;          |  (begin <Effect>* <Tail>)
;;;          |  (if <Pred> <Tail> <Tail>)
;;; Pred    --> (true)
;;;          |  (false)
;;;          |  (<relop> <Triv> <Triv>)
;;;          |  (begin <Effect*> <Pred>)
;;;          |  (if <Pred> <Pred> <Pred>)
;;; Effect  --> (nop)
;;;          |  (set! <Var> <Triv>)
;;;          |  (set! <Var> (<binop> <Triv> <Triv>))
;;;          |  (begin <Effect>+)
;;;          |  (if <Pred> <Pred> <Pred>)
;;; Var     --> <uvar>
;;;          |  <frame-var>
;;;          |  <register>
;;; Triv    --> <Var>
;;;          |  <int>
;;;          |  <label>
;;;
;;; Where uvar is symbol.n where (n >= 0)
;;;       binop is +, -, *, logand, logor, or sra
;;;       relop is <, <=, or =
;;;       register is rax, rcx, rdx, rbx, rbp, rdi, rsi, r8,
;;;                   r9, r10, r11, r12, r13, r14, or r15
;;;       label is symbol$n where (n >= 0)
;;;       frame-var is fvn where (n >= 0)
;;;
;;; If the value is a valid program, verify scheme returns the value
;;; unchanged; otherwise it signals an error.
;;;
;;; At this level in the compiler verify-scheme is also responsible for
;;; ensuring that machine constraints are not violated in generated
;;; assembler code to the best of its ability.

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
  (define FrameVar
    (lambda (x)
      (unless (frame-var? x)
        (error who "invalid frame-var ~s" x))
      x))
  (define Var
    (lambda (uvar*)
      (lambda (var)
        (unless (or (register? var) (frame-var? var) (uvar? var))
          (error who "invalid variable ~s" var))
        (when (uvar? var)
          (unless (memq var uvar*)
            (error who "unbound uvar ~s" var)))
        var)))
  (define Triv
    (lambda (label* uvar*)
      (lambda (t)
        (unless (or (register? t) (frame-var? t) (label? t) (uvar? t)
                    (and (integer? t) (exact? t)))
          (error who "invalid Triv ~s" t))
        (when (uvar? t)
          (unless (memq t uvar*)
            (error who "unbound uvar ~s" t)))
        (when (label? t)
          (unless (memq t label*)
            (error who "unbound label ~s" t)))
        t)))
  (define Pred
    (lambda (label* uvar*)
      (lambda (pr)
        (match pr
          [(true) (void)]
          [(false) (void)]
          [(begin ,[(Effect label* uvar*) -> ef*] ... ,[pr]) (void)]
          [(if ,[test] ,[conseq] ,[altern]) (void)]
          [(,relop ,[(Triv label* uvar*) -> x]
                    ,[(Triv label* uvar*) -> y])
           (unless (memq relop '(= < <= > >=))
             (error who "invalid predicate operator ~s" relop))
           (unless (or (and (or (register? x) (memq x uvar*))
                            (or (register? y)
                                (memq y uvar*)
                                (frame-var? y)
                                (int32? y)))
                       (and (frame-var? x)
                            (or (register? y)
                                (memq y uvar*)
                                (int32? y))))
             (error who "~s violates machine constraints"
                    `(,relop ,x ,y)))]
          [,pr (error who "invalid Pred ~s" pr)]))))
  (define Effect
    (lambda (label* uvar*)
      (lambda (ef)
        (match ef
          [(nop) (void)]
          [(set! ,[(Var uvar*) -> x]
             (,binop ,[(Triv label* uvar*) -> y]
                     ,[(Triv label* uvar*) -> z]))
           (unless (and (eq? y x)
                        (case binop
                          [(+ - logand logor)
                           (or (and (or (register? x) (memq x uvar*))
                                    (or (register? z)
                                        (memq z uvar*)
                                        (frame-var? z)
                                        (int32? z)))
                               (and (frame-var? x)
                                    (or (register? z)
                                        (memq z uvar*)
                                        (int32? z))))]
                          [(*)
                           (and (or (register? x) (memq x uvar*))
                                (or (register? z)
                                    (memq z uvar*)
                                    (frame-var? z)
                                    (int32? z)))]
                          [(sra)
                           (and (or (register? x) (frame-var? x) (memq x uvar*))
                                (uint6? z))]
                          [else
                            (error who "invalid binary operator ~s" binop)]))
             (error who "~s violates machine constraints"
                    `(set! ,x (,binop ,y ,z))))]
          [(set! ,[(Var uvar*) -> x] ,[(Triv label* uvar*) -> y])
           (unless (or (and (or (register? x) (memq x uvar*))
                            (or (register? y)
                                (memq y uvar*)
                                (frame-var? y)
                                (int64? y)
                                (label? y)))
                       (and (frame-var? x)
                            (or (register? y)
                                (memq y uvar*)
                                (int32? y))))
               (error who "~s violates machine constraints" `(set! ,x ,y)))]
          [(begin ,[ef] ,[ef*] ...) (void)]
          [(if ,[(Pred label* uvar*) -> test] ,[conseq] ,[altern]) (void)]
          [,ef (error who "invalid Effect ~s" ef)]))))
  (define Tail
    (lambda (label* uvar*)
      (lambda (tail)
        (match tail
          [(begin ,[(Effect label* uvar*) -> ef*] ... ,[tail]) (void)]
          [(if ,[(Pred label* uvar*) -> test] ,[conseq] ,[altern]) (void)]
          [(,[(Triv label* uvar*) -> t] ,[(Var uvar*)-> live-out*] ...)
           (when (integer? t)
             (error who "~s violates machine constraints" `(,t)))]
          [,tail (error who "invalid Tail ~s" tail)]))))
  (define Body
    (lambda (label*)
      (lambda (bd)
        (match bd
          [(locals (,uvar* ...) ,tail)
           (verify-x-list `(,uvar* ...) uvar? 'uvar)
           ((Tail label* uvar*) tail)]
          [,bd (error who "invalid Body ~s" bd)]))))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,bd*)] ...) ,bd)
       (verify-x-list label* label? 'label)
       (for-each (Body label*) bd*)
       ((Body label*) bd)]
      [,x (error who "invalid Program ~s" x)])
    x))

(define-who uncover-register-conflict
  (define add-conflicts!
    (lambda (ct lhs live*)
      (define add-conflict!
        (lambda (var1 var2)
          (let ([a (assq var1 ct)])
            (set-cdr! a (set-cons var2 (cdr a))))))
      (when (uvar? lhs)
        (for-each
          (lambda (live) (add-conflict! lhs live))
          live*))
      (for-each
        (lambda (live) (when (uvar? live) (add-conflict! live lhs)))
        live*)))
  (define Triv (lambda (x) (if (or (uvar? x) (register? x)) `(,x) '())))
  (define Effect*
    (lambda (x live* ct)
      (match x
        [() live*]
        [(,ef* ... ,ef) (Effect* ef* (Effect ef live* ct) ct)]
        [,x (error who "invalid Effect* list ~s" x)])))
  (define Effect
    (lambda (x live* ct)
      (match x
        [(nop) ---]
        [(if ,test ,[c-live*] ,[a-live*]) 
         (Pred test c-live* a-live* ct)]
        [(begin ,ef* ... ,[live*]) ---]
        [(set! ,lhs (,binop ,[Triv -> x-live*] ,[Triv -> y-live*]))
         ---]
        [(set! ,lhs ,rhs)
         ---]
        [,x (error who "invalid Effect list ~s" x)])))
  (define Pred
    (lambda (x t-live* f-live* ct)
      (match x
        [(true) ---]
        [(false) ---]
        [(if ,test ,[c-live*] ,[a-live*])
         ---]
        [(begin ,ef* ... ,[live*]) ---]
        [(,relop ,[Triv -> x-live*] ,[Triv -> y-live*])
         ---]
        [,x (error who "invalid Pred ~s" x)])))
  (define Tail
    (lambda (x ct)
      (match x
        [(begin ,ef* ... ,[live*]) ---]
        [(if ,test ,[c-live*] ,[a-live*]) 
         ---]
        [(,[Triv -> target-live*] ,live* ...)
         ---]
        [,x (error who "invalid Tail ~s" x)])))
  (define Body
    (lambda (x)
      (match x
        [(locals (,uvar* ...) ,tail)
         ;; set up the conflict table ct for storing conflicts
         (let ([ct (map (lambda (x) (cons x '())) uvar*)])
           (Tail tail ct)
           `(locals (,uvar* ...) 
              (register-conflict ,ct ,tail)))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))

(define-who assign-registers
  (define find-used
    (lambda (conflict* home*)
      ---))
  (define select-register
    (lambda (var conflict* home*)
      (let ([used* (find-used conflict* home*)])
        (let ([available* ---])
          (and (not (null? available*)) (car available*))))))
  (define rem-conflicts!
    (lambda (ct var conflict*)
      (for-each
        (lambda (x)
          (when (uvar? x)
            (let ([a (assq x ct)])
              (set-cdr! a (remq var (cdr a))))))
        conflict*)))
  (define find-homes
    (lambda (var* ct)
      (define k (length registers))
      (define low-degree?
        (lambda (var)
          (< (length (cdr (assq var ct))) k)))
      (let f ([var* var*])
        (if (null? var*)
            '()
            (let ([var ---])
              (let ([conflict* (cdr (assq var ct))] [var* (remq var var*)])
                (rem-conflicts! ct var conflict*)
                (let ([home* (f var*)])
                  (let ([reg (select-register var conflict* home*)])
                    (if reg
                        (cons `[,var ,reg] home*)
                        home*)))))))))
  (define Body
    (lambda (x)
      (match x
        [(locals (,uvar* ...) (register-conflict ,ct ,tail))
         (let ([home* (find-homes uvar* ct)])
           (let ([spill* (difference uvar* (map car home*))])
             (if (null? spill*)
                 `(locate (,home* ...) ,tail)
                 (error who "unable to assign registers to ~s" spill*))))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))

(define-who discard-call-live
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,ef* ... ,[tail]) `(begin ,ef* ... ,tail)]
        [(if ,test ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(,t ,live* ...) `(,t)]
        [,tail (error who "invalid Tail ~s" tail)])))
  (define Body
    (lambda (bd)
      (match bd
        [(locate ([,uvar* ,loc*] ...) ,[Tail -> tail])
         `(locate ([,uvar* ,loc*] ...) ,tail)]
        [,bd (error who "invalid Body ~s" bd)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> bd*])] ...) ,[Body -> bd])
       `(letrec ([,label* (lambda () ,bd*)] ...) ,bd)]
      [,x (error who "invalid Program ~s" x)])))
