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
