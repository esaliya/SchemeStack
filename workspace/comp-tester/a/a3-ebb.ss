(define-who expose-basic-blocks
  (define (Tail x)
    (match x
      [(if ,pred ,[conseq cb*] ,[altern ab*])
       (let ([clab (unique-label 'c)] [alab (unique-label 'a)])
         (let-values ([(pred pb*) (Pred pred clab alab)])
           (values pred
             `(,pb* ...
                [,clab (lambda () ,conseq)]
                ,cb* ...
                [,alab (lambda () ,altern)]
                ,ab* ...))))]
      [(begin ,effect* ... ,[tail tb*])
       (let-values ([(x xb*) (Effect* effect* `(,tail))])
         (values x `(,xb* ... ,tb* ...)))]
      [(,triv) (values `(,triv) '())]
      [,x (error who "malformed Tail ~s" x)]))
  (define (Pred x tlab flab)
    (match x
      [(true) (values `(,tlab) '())]
      [(false) (values `(,flab) '())]
      [(,relop ,triv1, triv2) (values
                                `(if (,relop ,triv1 ,triv2) (,tlab) (,flab))
                                '())]
      [(if ,pred ,cpred ,apred) 
       (let* ([cplab (unique-label 'c)] [aplab (unique-label 'a)])
         (let*-values ([(cpred cpb*) (Pred cpred tlab flab)]
                       [(apred apb*) (Pred apred tlab flab)]
                       [(pred pb*) (Pred pred cplab aplab)])
           (values pred
             `(,pb* ...                
                [,cplab (lambda () ,cpred)]
                ,cpb* ...
                [,aplab (lambda () ,apred)]
                ,apb* ...))))]
      [(begin ,ef* ... ,pred)
       (let*-values ([(pred pb*) (Pred pred tlab flab)]
                     [(x xb*) (Effect ef* `(,pred))])
         (values x
           `(,xb* ... ,pb* ...)))]
      [,x (error who "malformed Pred ~s" x)]))
  (define (Effect* x* tail*)
    (match x*
      [() (values (make-begin tail*) '())]
      [(,x* ... (set! ,a (,binop ,a ,b)))
       (Effect* x* `((set! ,a (,binop ,a ,b)) ,tail* ...))]
      [(,x* ... (set! ,var ,rhs))
       (Effect* x* `((set! ,var ,rhs) ,tail* ...))]
      [(,x* ... (if ,pred ,ef1 ,ef2))
       (let* ([jlab (unique-label 'j)]
              [join `(lambda () ,(make-begin tail*))]
              [clab (unique-label 'c)]
              [alab (unique-label 'a)])
         (let*-values ([(conseq cb*) (Effect* `(,ef1) `((,jlab)))]
                       [(altern ab*) (Effect* `(,ef2) `((,jlab)))]
                       [(pred pb*) (Pred pred clab alab)]
                       [(x xb*) (Effect* x* `(,pred))])
           (values x
             `(,xb* ... ,pb* ...
                [,clab (lambda () ,conseq)]
                ,cb* ...
                [,alab (lambda () ,altern)]
                ,ab* ...
                [,jlab ,join]))))]
 
      ; no need to handle ending effect separately since
      ; we have verified the source already
      [(,x* ... (begin ,ef* ...))
       (let*-values ([(x xb*) (Effect* ef* tail*)]
                     [(y yb*) (Effect* x* `(,x))])
         (values y `(,xb* ... ,yb* ...)))]
      [(,x* ... (nop))
       (Effect* x* tail*)]
      [,x (error who "malformed Effect ~s" x)]))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Tail -> tail* b**])] ...) ,[Tail -> tail b*])
       `(letrec ([,label* (lambda () ,tail*)] ... ,b** ... ... ,b* ...) ,tail)]
      [,x (error who "malformed Program ~s" x)])))