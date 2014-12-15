; Saliya Ekanayake
; sekanaya
; Assignment C

;---------------------------------------------------------------
; Input Language: 
;   Program	  --> Expr
;   Expr      --> label
;              |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([label (lambda (uvar*) 
;                                   (bind-free (uvar*) Expr))]*)
;                   (closures ([uvar label uvar*]*) Expr))
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who uncover-well-known
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                         < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                         set-car! set-cdr! vector-set!))
  (define remove-common
    (lambda (s)
      (cond
        [(null? s) '()]
        [else (cons (car s) (remove-common (remq (car s) (cdr s))))])))
  (define (Expr ex)
    (match ex
      [(begin ,[ex* nw**] ... ,[ex nw*])
       (values (make-begin `(,ex* ... ,ex)) 
         (remove-common `(,nw** ... ... ,nw* ...)))]
      [(if ,[pred pnw*] ,[conseq cnw*] ,[alter anw*])
       (values `(if ,pred ,conseq ,alter) 
         (remove-common `(,pnw* ... ,cnw* ... ,anw* ...)))]
      [(quote ,imm) (values `(quote ,imm) '())]
      [(let ([,uvar* ,[ex* nw**]] ...) ,[ex nw*])
       (values `(let ([,uvar* ,ex*] ...) ,ex)
         (remove-common `(,nw** ... ... ,nw* ...)))]
      [(letrec ([,label* (lambda (,fml** ...) 
                           (bind-free (,uvar** ...) ,[ex* nw**]))] ...)
         (closures ([,cp* ,lb* ,f** ...] ...) ,[ex nw*]))
       (let ([nw* (remove-common `(,nw** ... ... ,nw* ...))])
         (let ([wk* (difference cp* nw*)])
           (values `(letrec ([,label* (lambda (,fml** ...)
                                        (bind-free (,uvar** ...) ,ex*))] ...)
                      (closures ([,cp* ,lb* ,f** ...] ...)
                        (well-known ,wk* ,ex)))
             (difference nw* cp*))))]
      [,uvar (guard (uvar? uvar)) (values uvar `(,uvar))]
      [,label (guard (label? label)) (values label '())]
      [(,prim ,[ex* nw**] ...) (guard (memq prim primitives))
       (values `(,prim ,ex* ...) (remove-common `(,nw** ... ...)))]
      [(,label ,cp ,[rand* nw**] ...) (guard (label? label) (uvar? cp))
       (values `(,label ,cp ,rand* ...) (remove-common `(,nw** ... ...)))]
      [(,[rator nw*] ,[rand* nw**] ...)
       (values `(,rator ,rand* ...) (remove-common `(,nw* ... ,nw** ... ...)))]
      [,x (error who "invalid Expr ~s" x)]))
  (lambda (x)
    (match x
      [,[Expr -> ex nw*] ex])))
;---------------------------------------------------------------


;---------------------------------------------------------------
; Input Language: 
;   Program	  --> Expr
;   Expr      --> label
;              |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([label (lambda (uvar*) 
;                                   (bind-free (uvar*) Expr))]*)
;                   (closures ([uvar label uvar*]*)
;                     (well-known (uvar*) Expr)))
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who optimize-free
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                         < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                         set-car! set-cdr! vector-set!))
  (define remove-common
    (lambda (s)
      (cond
        [(null? s) '()]
        [else (cons (car s) (remove-common (remq (car s) (cdr s))))])))
  
  (define-record node (name free*) ([wkmt #t] [link* '()]))
  
  ;; cfree** is the list of free variables of each closure in closures form
  (define (prune-free name* cfree** wk* wkmt*)
    ;; free** is the list of "known to be free" variables
    (let ([free** (map (let ([x* (remove-common `(,@wkmt* ,@name*))])
                         (lambda (free*) (difference free* x*))) cfree**)])
      ;; nbnd* is a set of node bindings of the (name . node) form
      (let ([nbnd* (map (lambda (name free*) 
                          `(,name . ,(make-node name free*))) name* free**)])
        ;; add links
        (for-each
          (lambda (nbnd cfree*)
            (for-each
              (lambda (cfree)
                (let ([nb (assq cfree nbnd*)])
                  (if nb
                      (set-node-link*! (cdr nb)
                        (cons (cdr nbnd) (node-link* (cdr nb)))))))
              cfree*))
          nbnd* cfree**)
        
        ;; Process each record and propage info to other nodes
        (for-each 
          (letrec ([f (lambda (nbnd)
                        (if (node-wkmt (cdr nbnd))
                            (if (or (not (memq (car nbnd) wk*))
                                    (not (null? (node-free* (cdr nbnd)))))
                                (begin
                                  (set-node-wkmt! (cdr nbnd) #f)
                                  (for-each
                                    (lambda (node)
                                      (set-node-free*! node (cons (car nbnd) (node-free* node)))
                                      (f (assq (node-name node) nbnd*)))
                                    (node-link* (cdr nbnd)))))))]) 
            f)
          nbnd*)
        
        ;; Extract info on final free** and wkmt*
        (let ([free** (map (lambda (nbnd) (node-free* (cdr nbnd))) nbnd*)])
          (let loop ([nbnd* nbnd*] [wkmt* wkmt*])
            (if (null? nbnd*)
                (values free** wkmt*)
                (if (node-wkmt (cdar nbnd*))
                    (loop (cdr nbnd*) (cons (caar nbnd*) wkmt*))
                    (loop (cdr nbnd*) wkmt*))))))))
    
  (define (Expr wkmt*)
    (lambda (ex)
      (match ex
        [(begin ,[ex*] ... ,[ex])
         (make-begin `(,ex* ... ,ex))]
        [(if ,[pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(quote ,imm) `(quote ,imm)]
        [(let ([,uvar* ,[ex*]] ...) ,[ex])
         `(let ([,uvar* ,ex*] ...) ,ex)]
        [,uvar (guard (uvar? uvar)) uvar]
        ;; The order of letrec bindings and closures are assumed to be the same
        [(letrec ([,lb* (lambda (,cp* ,fml** ...) (bind-free (,cp* ,free** ...) ,ex*))] ...)
           (closures ([,name* ,lb* ,free** ...] ...)
             (well-known (,wk* ...) ,ex)))
         ;; free** in LHS will be the new list of lists with free variables for each closure  
        (let-values ([(free** wkmt*) (prune-free name* free** wk* wkmt*)])
          ;; cs* is the filtered set of closures, which doesn't have wkmt closures
          ;; wkmtlb* is the list of labels for wkmt closures
          (let (
                [cs* (filter (lambda (cs) (not (memq (car cs) wkmt*)))
                             `((,name* ,lb* ,free** ...) ...))]
                [wkmtlb* (map cdr (filter (lambda (bnd) (memq (car bnd) wkmt*))
                                          `((,name* . ,lb*) ...)))]
                [ex* (map (Expr wkmt*) ex*)]
                [ex ((Expr wkmt*) ex)])
            ;; bnd* is the list of new letrec bindings
            (let ([bnd* (map (lambda (lb cp fml* free* ex)
                               (if (memq lb wkmtlb*)
                                   `(,lb (lambda (,fml* ...) (bind-free (dummy) ,ex)))
                                   `(,lb (lambda (,cp ,fml* ...) (bind-free (,cp ,free* ...) ,ex)))))
                             lb* cp* fml** free** ex*)])
              `(letrec ,bnd* (closures ,cs* ,ex)))))]
        [,label (guard (label? label)) label]
        [(,prim ,[ex*] ...) (guard (memq prim primitives)) `(,prim ,ex* ...)]
        ;; Handle direct calls separately to remove possible well-known empty case.
        ;; If the name is of a well-known empty closure then this will remove it.
        [(,label ,name ,[rand*] ...) (guard (label? label) (uvar? name))
         (if (memq name wkmt*) `(,label ,rand* ...) `(,label ,name ,rand* ...))]
        [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (match x
      [,[(Expr '()) -> ex] ex]))) 
;---------------------------------------------------------------

  
;---------------------------------------------------------------
; Input Language: 
;   Program	  --> Expr
;   Expr      --> label
;              |  uvar
;              |  (quote Immediate)
;              |  (if Expr Expr Expr)
;              |  (begin Expr* Expr)
;              |  (let ([uvar Expr]*) Expr)
;              |  (letrec ([label (lambda (uvar*) 
;                                   (bind-free (uvar*) Expr))]*)
;                   (closures ([uvar label uvar*]*) Expr))
;              |  (prim Expr*)
;              |  (Expr Expr*)
;   Immediate --> fixnum | () | #t | #f
;
;   prim:
;     +, -, *, car, cdr, cons, make-vector, vector-length, vector-ref,
;     make-procedure, procedure-ref, procedure-code, void, 
;     <, <=, =, >=, >, boolean?, eq?, procedure?, fixnum?, null?, pair?, vector?
;     set-car!, set-cdr!, vector-set!, procedure-set!
;---------------------------------------------------------------
(define-who optimize-self-reference
  (define primitives '(+ - * car cdr cons make-vector vector-length vector-ref void
                         < <= = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                         set-car! set-cdr! vector-set!))
  (define (Lambda name-cp* name)
    (lambda (lamb)
      (match lamb
        [(lambda (,fml* ...) (bind-free (,cp ,[(Expr name-cp*) -> f*] ...) ,ex))
         (let ([ex (if name 
                       ((Expr (cons `(,name . ,cp) name-cp*)) ex)
                       ((Expr name-cp*) ex))])
           `(lambda (,fml* ...) 
              (bind-free (,cp ,(if name (remq name f*) f*) ...) ,ex)))]
        [,x (error who "invalid Lambda ~s" x)])))
  (define (Expr name-cp*)
    (lambda (ex)
      (match ex
        [(begin ,[ex*] ... ,[ex])
         (make-begin `(,ex* ... ,ex))]
        [(if ,[pred] ,[conseq] ,[alter])
         `(if ,pred ,conseq ,alter)]
        [(quote ,imm) `(quote ,imm)]
        [(let ([,uvar* ,[ex*]] ...) ,[ex])
         `(let ([,uvar* ,ex*] ...) ,ex)]
        [(letrec ([,label* ,lamb*] ...)            
           (closures ([,name* ,lb* ,[f**] ...] ...) ,[ex]))
         (let ([bnd* `((,lb* . (,name* ,f** ...)) ...)])
           (let ([lamb* (map 
                         (lambda (label lamb)
                           (let ([bnd (assq label bnd*)])
                             (if bnd
                                 (if (memq (cadr bnd) (cddr bnd))
                                     ((Lambda name-cp* (cadr bnd)) lamb)
                                     ((Lambda name-cp* #f) lamb))
                                 ((Lambda name-cp* #f) lamb))))
                         label* lamb*)])
             `(letrec ([,label* ,lamb*] ...)
                (closures ([,name* ,lb* ,(map remq name* f**) ...] ...) ,ex))))]
        [,uvar (guard (uvar? uvar))
          (if (not (null? name-cp*))
              (let ([name-cp (assq uvar name-cp*)])
                (if name-cp (cdr name-cp) uvar))
              uvar)]
        [,label (guard (label? label)) label]
        [(,prim ,[ex*] ...) (guard (memq prim primitives))
         `(,prim ,ex* ...)]
        [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (match x
      [,[(Expr '()) -> ex] ex])))