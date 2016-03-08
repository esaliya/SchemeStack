;;; Andy Keep, Kent Dybvig
;;; P423/P523
;;; Spring 2010

;;; verify-scheme accepts a single value and verifies that the value
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

;;; See the assignment description for our documentation for this pass

(define-who expose-frame-var
  (define Triv
    (lambda (t)
      (if (frame-var? t)
          (make-disp-opnd 'rbp (ash (frame-var->index t) 3))
          t)))
  (define Effect
    (lambda (st)
      (match st
        [(set! ,[Triv -> var] (,binop ,[Triv -> t1] ,[Triv -> t2]))
         `(set! ,var (,binop ,t1 ,t2))]
        [(set! ,[Triv -> var] ,[Triv -> t])
         `(set! ,var ,t)]
        [,st (error who "invalid syntax for Effect ~s" st)])))
  (define Tail
    (lambda (tail)
      (match tail
        [(,[Triv -> t]) `(,t)]
        [(begin ,[Effect -> ef*] ... ,[tail])
         `(begin ,ef* ... ,tail)]
        [,tail (error who "invalid syntax for Tail ~s" tail)])))
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
       `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)]
      [,program (error who "invalid syntax for Program: ~s" program)])))

;;; See the assignment description for our documentation for this pass

(define-who generate-x86-64
  (define prim->opcode
    (lambda (prim)
      (cdr (assq prim
             '((+ . addq) (- . subq) (* . imulq)
               (logand . andq) (logor . orq) (sra . sarq))))))
  (define Code
    (lambda (ef)
      (match ef
        [,lab (guard (label? lab)) (emit-label lab)]
        [(jump ,rand) (emit-jump 'jmp rand)]
        [(set! ,rand1 ,lab)
         (guard (label? lab))
         (emit 'leaq lab rand1)]
        [(set! ,rand1 (,prim ,rand1 ,rand2))
         (emit (prim->opcode prim) rand2 rand1)]
        [(set! ,rand1 ,rand2) (emit 'movq rand2 rand1)]
        [,ef (error who "invalid Code syntax ~s" ef)])))
  (lambda (x)
    (match x
      [(code ,code* ...) (emit-program (for-each Code code*))]
      [,x (error who "invalid Program syntax ~s" x)])))
