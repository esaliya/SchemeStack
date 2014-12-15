;; --------------------------------------------------------------------------------
;; Q1.)
;; --------
;; I ran into an issue on understanding the use of ... with match. 
;; Here's a example case that depicts this.

;; 1. (match '(a 17 37) [(a ,x* ...) x*]) => (17 37)
;; 2. (match '(a 17 37) [(a ,x* ...) `(,x* ...)]) => (17 37)

;; The first case shows that x* is a list, but when you use ... with x* 
;; as in the second case it has splice the values into surrounding list structure. 
;; Am I understanding this correct? Yes
;; 
;; Ans.
;; --------
;; One useful feature of quasiquote not described in these documents is a match extension
;; that allows ellipses to be used in place of unquote-splicing, which often leads to more 
;; readable code.
;;(define translate
;;  (lambda (x)
;;    (match x
;;      [(let ((,var* ,expr*) ...) ,body ,body* ...)
;;       `((lambda ,var* ,body ,body* ...) ,expr* ...)]
;;      [,x (error 'translate "invalid expression: ~s" x)])))
;; 
;; Compare this with,
;; 
;;  (define translate
;;  (lambda (x)
;;    (match x
;;      [(let ((,var* ,expr*) ...) ,body ,body* ...)
;;       `((lambda ,var* ,body ,@body*) ,@expr*)]
;;      [,x (error 'translate "invalid expression: ~s" x)]))) 
;; --------------------------------------------------------------------------------


;; --------------------------------------------------------------------------------
;; Q2.)
;; --------
;; ,[x* ...] Vs ,[x*] ...
;;  
;; Ans.
;; -------- 
;; :) This is funny, I wonder how I lost this.  ... in the first case is used
;; to tell you can write more stuff (although * is not necessary). The second
;; case uses ... as a keyword to say there will be more to match for x*. So 
;; first ... is like when you write bla bla bla ... :)
;; -------------------------------------------------------------------------------- 


;; --------------------------------------------------------------------------------
;; Q3.)
;; --------
;; Can we use scheme to write a compiler for non paranthesis language?
;; e.g.
;; (match 'if (x < 0) something
;;    [if (,x ,op ,y) ,cons 'cool]) <== we can't use as it is
;; 
;;  
;; Ans.
;; -------- 
;; Not with scheme's match at present.
;; -------------------------------------------------------------------------------- 


;; --------------------------------------------------------------------------------
;; Q4.)
;; --------
;; Can I use Cat form effectively for pred? The method Pred takes pred, tlab, flab
;; and returns pred, pb*
;; 
;; [(begin ,ef* ... ,pred)
;;       (let*-values ([(pred pb*) (Pred pred tlab flab)]
;;                     [(x xb*) (Effect ef* `(,pred))])
;;         (values x
;;           `(,xb* ... ,pb* ...)))]
;; 
;; Also for ef* here,
;; 
;;
;; Ans.
;; -------- 
;; Yep, the reason is cata won't call the method, but just use whatever following
;; "," when recurring to match again. Whatever extra arguments you want will be the
;; ones you got originally when you call the method itself. So this is a tricky 
;; business and works only if you are happy to use the original extra arguments
;; when recurring to match.
;; -------------------------------------------------------------------------------- 

;; --------------------------------------------------------------------------------
;; Q4.)
;; --------
;; What is (let loop ([set1 set2]) ...) form in the definition of union in
;; helpers.ss?
;;
;; Ans.
;; --------
;; named let, similar to letrec kinda thing 
;; --------------------------------------------------------------------------------
;; 

;; --------------------------------------------------------------------------------
;; Q5.)
;; --------
;; Some interesting work on remq/eq and objects and refs
;; (let ([s '((a rax b c) (b a r11) (c r15 a rax))])
;;    (let ([pick (cadr s)])
;;      (let ([m (map (lambda (row)
;;                      (cons (car row) (remq (car pick) (cdr row)))) (begin (printf "\n~s\n\n" (remq pick s)) (remq '(b a r11) s)))])
;;        m)))
;;
;;((a rax b c) (c r15 a rax))
;;
;;((a rax c) (b a r11) (c r15 a rax))
;; 
;; -----------------------------------------------------------------------------------------
;;> (let ([cg '((x.1 rax x.2 r11 rcx) (x.2 x.1 x.3) (x.3 x.2))])
;;    (let ([pick (cadr cg)])
;;      (let* ([r (remq pick cg)] [s (remq (car pick) (car r))])
;;        (printf "\n***********cg***********\n~s\n************s***********\n~s\n" cg s)
;;        (eq? (car pick) (caddar r)))))
;;
;;***********cg***********
;;((x.1 rax x.2 r11 rcx) (x.2 x.1 x.3) (x.3 x.2))
;;************s***********
;;(x.1 rax r11 rcx)
;;#t
;;> (let ([cg '((x.1 rax (x.2) r11 rcx) ((x.2) x.1 x.3) (x.3 x.2))])
;;    (let ([pick (cadr cg)])
;;      (let* ([r (remq pick cg)] [s (remq (car pick) (car r))])
;;        (printf "\n***********cg***********\n~s\n************s***********\n~s\n" cg s)
;;        (eq? (car pick) (caddar r)))))
;;
;;***********cg***********
;;((x.1 rax (x.2) r11 rcx) ((x.2) x.1 x.3) (x.3 x.2))
;;************s***********
;;(x.1 rax (x.2) r11 rcx)
;;#f
;;
;;  
;; --------------------------------------------------------------------------------

;; --------------------------------------------------------------------------------
;; Q5.)
;; --------
;; What is the way to remove an element from a list while modifiying the 
;; original list?
;;
;; Ans.
;; --------
;;  
;; --------------------------------------------------------------------------------

;; --------------------------------------------------------------------------------
;; Q6.)
;; --------
;; Optimizing labels that jumps to registers? a11 - optimize-jumps
;;
;; Ans.
;; --------
;;  
;; --------------------------------------------------------------------------------

;; --------------------------------------------------------------------------------
;; Q7.)
;; --------
;; Identifying the presence of ratorcp in introduce-procedure-primitives
;; since an optimization as in Challenge C may have removed the need for
;; a closure pointer.
;;
;; Ans.
;; --------
;;  
;; --------------------------------------------------------------------------------
