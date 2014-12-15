;---------------------------------------------------------------
;;; verify-a11-output accept a single value and verifies that the value
;;; is a valid program in the current source language.
;;;
;;; Grammar for verify-a11-output ,i.e. input to a10 passes (assignment 11):
;;;
;;;  Program --> (letrec ([<label> (lambda (<uvar>*) <Value>)]*) <Value>)
;;;  Value   --> <label>
;;;           |  <uvar>
;;;           |  (quote <Immediate>)
;;;           |  (if <Pred> <Value> <Value>)
;;;           |  (begin <Effect>* <Value>)
;;;           |  (let ([<uvar> <Value>]*) <Value>)
;;;           |  (<value-prim> <Value>*)
;;;           |  (<Value> <Value>*)
;;;  Pred    --> (true)
;;;           |  (false)
;;;           |  (if <Pred> <Pred> <Pred>)
;;;           |  (begin <Effect>* <Pred>)
;;;           |  (let ([<uvar> <Value>]*) <Pred>)
;;;           |  (<pred-prim> <Value>*)
;;;  Effect  --> (nop)
;;;           |  (if <Pred> <Effect> <Effect>)
;;;           |  (begin <Effect>* <Effect>)
;;;           |  (let ([<uvar> <Value>]*) <Effect>)
;;;           |  (<effect-prim> <Value>*)
;;;           |  (<Value> <Value>*)
;;;  Immediate -> <fixnum> | () | #t | #f
;;;
;;; Where uvar is symbol.n, n >= 0
;;;       label is symbol$n, n >= 0
;;;       fixnum is an exact integer
;;;       value-prims are void (zero arguments); car, cdr, vector-length,
;;;         make-vector (one argument); *, +, -, cons, vector-ref
;;;         (two arguments)
;;;       pred-prims are boolean?, fixnum?, null?, pair?, vector?
;;;         (one argument); <, <=, =, >=, >, eq? (two arguments)
;;;       effect-prims are set-car!, set-cdr! (two arguments);
;;;         vector-set! (three arguments)
;;;
;;; Each label bound by the letrec expression must have a unique suffix,
;;; and each uvar bound by a lambda or let expression must have a unique
;;; suffix, within the same Program.
;;;
;;; Machine constraints:
;;;   - each fixnum must be an exact integer n, -2^(k-1) <= n <= 2^(k-1)-1,
;;;     where k is the value of the helpers.ss variable fixnum-bits
;;;
;;; If the value is a valid program, verify-scheme returns the value
;;; unchanged; otherwise it signals an error.
;---------------------------------------------------------------
(define-who verify-a11-output
  (define value-prims
    '((* . 2) (+ . 2) (- . 2) (car . 1) (cdr . 1) (cons . 2)
       (make-vector . 1) (vector-length . 1) (vector-ref . 2)
       (make-procedure . 2) (procedure-ref . 2) (procedure-code . 1)
       (void . 0)))
  (define pred-prims
    '((< . 2) (<= . 2) (= . 2) (>= . 2) (> . 2) (boolean? . 1)
       (eq? . 2) (fixnum? . 1) (null? . 1) (pair? . 1)
       (vector? . 1) (procedure? . 1)))
  (define effect-prims '((set-car! . 2) (set-cdr! . 2) (vector-set! . 3) (procedure-set! . 3)))
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
  (define Program
    (lambda (x)
      (define all-uvar* '())
      (define Body
        (lambda (label* fml*)
          (define (Immediate imm)
            (cond
              [(memq imm '(#t #f ())) (values)]
              [(and (integer? imm) (exact? imm))
               (unless (fixnum-range? imm)
                 (error who "integer ~s is out of fixnum range" imm))
               (values)]
              [else (error who "invalid Immediate ~s" imm)]))
          (define Value
            (lambda (uvar*)
              (lambda (val)
                (match val
                  [,label (guard (label? label))
                   (if (memq label label*)
                       (values)
                       (error who "unbound label ~s" label))]
                  [,uvar (guard (uvar? uvar))
                   (if (memq uvar uvar*)
                       (values)
                       (error who "unbound uvar ~s" uvar))]
                  [(quote ,[Immediate ->]) (values)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(let ([,new-uvar* ,[]] ...) ,val)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Value (append new-uvar* uvar*)) val)]
                  [(,prim ,x* ...)
                   (guard (assq prim value-prims))
                   (unless (= (length x*) (cdr (assq prim value-prims)))
                     (error who "too many or few arguments ~s for ~s" (length x*) prim))
                   (for-each (Value uvar*) x*)
                   (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Value ~s" `(,x ,y ...))]
                  [(,[] ,[] ...) (values)]
                  [,val (error who "invalid Value ~s" val)]))))
          (define Effect
            (lambda (uvar*)
              (lambda (ef)
                (match ef
                  [(nop) (values)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[] ... ,[]) (values)]
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,ef)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Effect (append new-uvar* uvar*)) ef)]
                  [(,prim ,x* ...)
                   (guard (assq prim effect-prims))
                   (unless (= (length x*) (cdr (assq prim effect-prims)))
                     (error who "too many or few arguments ~s for ~s" (length x*) prim))
                   (for-each (Value uvar*) x*)
                   (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Effect ~s" `(,x ,y ...))]
                  [(,[(Value uvar*) ->] ,[(Value uvar*) ->] ...) (values)]
                  [,ef (error who "invalid Effect ~s" ef)]))))
          (define Pred
            (lambda (uvar*)
              (lambda (pr)
                (match pr
                  [(true) (values)]
                  [(false) (values)]
                  [(if ,[] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,pr)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Pred (append new-uvar* uvar*)) pr)]
                  [(,prim ,x* ...)
                   (guard (assq prim pred-prims))
                   (unless (= (length x*) (cdr (assq prim pred-prims)))
                     (error who "too many or few arguments ~s for ~s" (length x*) prim))
                   (for-each (Value uvar*) x*)
                   (values)]
                  [,pr (error who "invalid Pred ~s" pr)]))))
            (lambda (x) ((Value fml*) x))))
      (define Lambda
        (lambda (label*)
          (lambda (x)
            (match x
              [(lambda (,fml* ...) ,[(Body label* fml*) ->])
               (set! all-uvar* (append fml* all-uvar*))
               (values)]
              [,x (error who "invalid Lambda ~a" x)]))))
      (match x
        [(letrec ([,label* ,[(Lambda label*) ->]] ...) ,[(Body label* '()) ->])
         (verify-x-list label* label? 'label)
         (verify-x-list all-uvar* uvar? 'uvar)]
        [,x (error who "invalid Program ~s" x)])))
  (lambda (x) (Program x) x))
;---------------------------------------------------------------


;---------------------------------------------------------------
;;; Andy Keep, Kent Dybvig
;;; P423/P523
;;; Spring 2010

;;; verify-a10-output accept a single value and verifies that the value
;;; is a valid program in the current source language.
;;;
;;; Grammar for verify-a10-output ,i.e. input to a9 passes (assignment 11):
;;;
;;;  Program --> (letrec ([<label> (lambda (<uvar>*) <Tail>)]*) <Tail>)
;;;  Tail    --> <Triv>
;;;           |  (binop <Value> <Value>)
;;;           |  (alloc <Value>)
;;;           |  (<Value> <Value>*)
;;;           |  (if <Pred> <Tail> <Tail>)
;;;           |  (begin <Effect>* <Tail>)
;;;           |  (let ([<uvar> <Value>]*) <Tail>)
;;;  Pred    --> (true)
;;;           |  (false)
;;;           |  (<relop> <Value> <Value>)
;;;           |  (if <Pred> <Pred> <Pred>)
;;;           |  (begin <Effect>* <Pred>)
;;;           |  (let ([<uvar> <Value>]*) <Pred>)
;;;  Effect  --> (nop)
;;;           |  (mset! <Value> <Value> <Value>)
;;;           |  (<Value> <Value>*)
;;;           |  (if <Pred> <Effect> <Effect>)
;;;           |  (begin <Effect>* <Effect>)
;;;           |  (let ([<uvar> <Value>]*) <Effect>)
;;;  Value   --> <Triv>
;;;           |  (<binop> <Value> <Value>)
;;;           |  (alloc <Value>)
;;;           |  (<Value> <Value>*)
;;;           |  (if <Pred> <Value> <Value>)
;;;           |  (begin <Effect>* <Value>)
;;;           |  (let ([<uvar> <Value>]*) <Value>)
;;;  Triv    --> <uvar> | <integer> | <label>
;;;
;;; Where uvar is symbol.n, n >= 0
;;;       binop is mref +, -, *, logand, logor, or sra
;;;       relop is <, <=, =, >=, >
;;;       label is symbol$n, n >= 0
;;;
;;; Each label bound by the letrec expression must have a unique suffix,
;;; and each uvar bound by a lambda or let expression must have a unique
;;; suffix, within the same Program.
;;;
;;; Machine constraints:
;;;   - sra's second operand must be an exact integer k, 0 <= k <= 63
;;;   - each other integer must be a exact integer n, -2^63 <= n <= 2^63-1
;;;
;;; If the value is a valid program, verify-scheme returns the value
;;; unchanged; otherwise it signals an error.
;---------------------------------------------------------------
(define-who verify-a10-output
  (define binops '(mref + - * logand logor sra))
  (define relops '(< > <= >= =))
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
  (define Program
    (lambda (x)
      (define all-uvar* '())
      (define Body
        (lambda (label* fml*)
          (define Triv
            (lambda (uvar*)
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
                (values))))
          (define Value
            (lambda (uvar*)
              (lambda (val)
                (match val
                  [(let ([,new-uvar* ,[]] ...) ,val)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Value (append new-uvar* uvar*)) val)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(sra ,[] ,y)
                   (unless (uint6? y)
                     (error who "invalid sra operand ~s" y))
                   (values)]
                  [(,binop ,[] ,[])
                   (guard (memq binop binops))
                   (values)]
                  [(alloc ,[]) (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Value ~s" `(,x ,y ...))]
                  [(,[] ,[] ...) (values)]
                  [,[(Triv uvar*) ->] (values)]))))
          (define Effect
            (lambda (uvar*)
              (lambda (ef)
                (match ef
                  [(nop) (values)]
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,ef)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Effect (append new-uvar* uvar*)) ef)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[] ... ,[]) (values)]
                  [(mset! ,[(Value uvar*) ->] 
                          ,[(Value uvar*) ->] 
                          ,[(Value uvar*) ->])
                   (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Effect ~s" `(,x ,y ...))]
                  [(,[(Value uvar*) ->] ,[(Value uvar*) ->] ...) (values)]
                  [,ef (error who "invalid Effect ~s" ef)]))))
          (define Pred
            (lambda (uvar*)
              (lambda (pr)
                (match pr
                  [(true) (values)]
                  [(false) (values)]
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,pr)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Pred (append new-uvar* uvar*)) pr)]
                  [(if ,[] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(,relop ,[(Value uvar*) ->] ,[(Value uvar*) ->])
                   (guard (memq relop relops))
                   (values)]
                  [,pr (error who "invalid Pred ~s" pr)]))))
          (define Tail
            (lambda (uvar*)
              (lambda (tail)
                (match tail
                  [(let ([,new-uvar* ,[(Value uvar*) ->]] ...) ,tail)
                   (set! all-uvar* (append new-uvar* all-uvar*))
                   ((Tail (append new-uvar* uvar*)) tail)]
                  [(if ,[(Pred uvar*) ->] ,[] ,[]) (values)]
                  [(begin ,[(Effect uvar*) ->] ... ,[]) (values)]
                  [(sra ,[(Value uvar*) ->] ,y)
                   (unless (uint6? y)
                     (error who "invalid sra operand ~s" y))
                   (values)]
                  [(,binop ,[(Value uvar*) ->] ,[(Value uvar*) ->])
                   (guard (memq binop binops))
                   (values)]
                  [(alloc ,[]) (values)]
                  [(,x ,y ...)
                   (guard (and (symbol? x) (not (or (uvar? x) (label? x)))))
                   (error who "invalid Tail ~s" `(,x ,y ...))]
                  [(,[(Value uvar*) ->] ,[(Value uvar*) ->] ...) (values)]
                  [,[(Triv uvar*) ->] (values)]))))
            (lambda (tail) ((Tail fml*) tail))))
    (define Lambda
      (lambda (label*)
        (lambda (x)
          (match x
            [(lambda (,fml* ...) ,[(Body label* fml*) ->])
             (set! all-uvar* (append fml* all-uvar*))
             (values)]
            [,x (error who "invalid Lambda ~a" x)]))))
    (match x
      [(letrec ([,label* ,[(Lambda label*) ->]] ...) ,[(Body label* '()) ->])
       (verify-x-list label* label? 'label)
       (verify-x-list all-uvar* uvar? 'uvar)]
      [,x (error who "invalid Program ~s" x)])))
  (lambda (x) (Program x) x))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Pass:           
;   optimize-jumps
;
; Description: 
;   Relies on the output of expose-basic-block pass. This is
;   an optimization pass, which will remove letrec bindings
;   that are pure jumps. 
;
; Input Language:  
;   Program	-->	(letrec ([label (lambda () Tail)]*) Tail)
;   Tail	-->	(Triv)
;	         |	(if (relop Triv Triv) (,label) (,label))
;	         |	(begin Effect* Tail)
;   Effect  -->	(set! Loc Triv)
;	         |	(set! Loc (binop Triv Triv))
;   Loc     -->	reg | disp-opnd | index-opnd
;   Triv	-->	Loc | int | label 
;
; Output Language: 
;   Program	-->	(letrec ([label (lambda () Tail)]*) Tail)
;   Tail	-->	(Triv)
;	         |	(if (relop Triv Triv) (,label) (,label))
;	         |	(begin Effect* Tail)
;   Effect  -->	(set! Loc Triv)
;	         |	(set! Loc (binop Triv Triv))
;   Loc     -->	reg | disp-opnd | index-opnd
;   Triv	-->	Loc | int | label
;---------------------------------------------------------------
(define-who optimize-jumps
  (define set-jumps!
    (lambda (junk* label target)
      (match junk*
        [() (void)]
        [([,l . ,t] ,j* ...)
         (begin
           (if (eq? label t) (set-cdr! (car junk*) target))
           (set-jumps! j* label target))])))
  (define list-junks
    (lambda (bnd* junk*)
      (match bnd*
        [() junk*]
        [([,l . (,t)] ,bnd* ...)
         (if (label? t)
             (let ([kv (assq t junk*)])
               (if kv
                   (if (eq? l (cdr kv))
                       (list-junks bnd* junk*)
                       (list-junks bnd* (cons `(,l . ,(cdr kv)) junk*)))
                   (begin (set-jumps! junk* l t)
                     (list-junks bnd* (cons `(,l . ,t) junk*)))))
             (list-junks bnd* junk*))]
        [([,l . ,t] ,bnd* ...) (list-junks bnd* junk*)])))
  (define (Triv junk*)
    (lambda (t)
      (match t
        [,l (guard (label? l)) 
         (let ([kv (assq l junk*)])
           (if kv (cdr kv) l))]
        [,x (guard (or (register? x) (disp-opnd? x)
                       (index-opnd? x) (integer? x))) x]
        [,x (error who "invalid Triv ~s" x)])))
  (define (Effect junk*)
    (lambda (ef)
      (match ef
        [(set! ,loc (,binop ,[(Triv junk*) -> x] ,[(Triv junk*) -> y]))
         `(set! ,loc (,binop ,x ,y))]
        [(set! ,loc ,[(Triv junk*) -> t])
         `(set! ,loc ,t)]
        [,x (error who "invalid Effect ~s" x)])))
  (define (Tail junk*)
    (lambda (tail)
      (match tail
        [(begin ,[(Effect junk*) -> ef*] ... ,[tail])
         (make-begin `(,ef* ... ,tail))]
        [(if (,relop ,[(Triv junk*) -> x] ,[(Triv junk*) -> y])
             ,[conseq] ,[alter])
         `(if (,relop ,x ,y) ,conseq ,alter)]
        [(,[(Triv junk*) -> t]) `(,t)]
        [,x (error who "invalid Tail ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
       (let ([bnd* `([,label* . ,tail*] ...)])
         (let ([junk* (list-junks bnd* '())])
           (let ([bnd* (filter (lambda (bnd) 
                                 (not (assq (car bnd) junk*))) bnd*)])
             `(letrec ([,(map car bnd*) 
                         (lambda () ,(map (lambda (bnd)
                                            ((Tail junk*) (cdr bnd)))
                                          bnd*))] ...)
                ,((Tail junk*) tail)))))])))  
;---------------------------------------------------------------