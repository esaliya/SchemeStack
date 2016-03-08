;;----------------------------------
;; B551 - Assignment 5
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    sekanaya
;; Email: sekanaya@cs.indiana.edu
;;----------------------------------

(define-syntax compound?
  (syntax-rules ()
    [(_ x) (and (pair? x) (symbol? (car x)))]))

(define-syntax args
  (syntax-rules ()
    [(_ x) (cdr x)]))

(define-syntax op
  (syntax-rules ()
    [(_ x) (car x)]))

(define-syntax rest
  (syntax-rules ()
    [(_ x) (cdr x)]))

(define-syntax first
  (syntax-rules ()
    [(_ x) (car x)]))

(define-syntax conseq
  (syntax-rules ()
    [(_ x) (cadddr x)]))

(define-syntax antecedents
  (syntax-rules ()
    [(_ x) (caddr x)]))

(define unify
  (lambda (x y theta)
    (cond
      [(not theta) #f]
      [(eq? x y) theta]
      [(var? x) (unify-var x y theta)]
      [(var? y) (unify-var y x theta)]
      [(and (compound? x) (compound? y))
       (unify (args x) (args y) (unify (op x) (op y) theta))]
      [(and (not (null? x)) (not (null? y)) (list? x) (list? y))
       (unify (rest x) (rest y) (unify (first x) (first y) theta))]
      [else #f])))

(define unify-var
  (lambda (v x theta)
    (let ([bnd (assq v theta)])
      (if bnd 
          (unify (cdr bnd) x theta)
          (let ([bnd (assq x theta)])
            (if bnd
                (unify v (cdr bnd) theta)
                (if (occur-check v x) #f (cons `(,v . ,x) theta))))))))

(define occur-check
  (lambda (v x)
    (and (not (eq? v x)) (pair? x) (contains? v x))))

(define-record-type node (fields state (mutable lastrule) (mutable lastgoal) (mutable depth) (mutable parent)))
(define-record-type state (fields goals theta))

(define no-goals?
  (lambda (node)
    (null? (state-goals (node-state node)))))

(define make-proof-state
  (lambda (goals theta)
    (make-state goals theta)))

(define get-next-proof-nodes
  (lambda (node rules)
    (let ([children '()]
          [goals (state-goals (node-state node))] 
          [theta (state-theta (node-state node))])
      (let forrules([rules rules] [children children])
        (if (null? rules) 
            children
            (let ([rule (standardize-variables (car rules))])
              (let forgoals ([goals goals] [children children])
                (if (not (null? goals))
                    (let ([goal (car goals)])
                      (let ([theta (unify goal (conseq rule) theta)])
                        (if theta
                            (forgoals (cdr goals)
                                      (cons (make-node
                                             (make-state
                                              `(,@(remq goal (state-goals (node-state node)))
                                                  ,@(map (lambda (ant) (replace-vars ant theta)) (antecedents rule)))
                                              theta)
                                             rule (replace-vars goal theta) (add1 (node-depth node)) node)
                                            children))
                            (forgoals (cdr goals) children))))
                    (forrules (cdr rules) children)))))))))


(define replace-vars
  (lambda (sentence theta)
    (map (lambda (x) (walk x theta)) sentence)))

(define walk
  (lambda (v s)
    (cond
      ((var? v)
       (let ((a (assq v s)))
         (cond
           (a (walk (cdr a) s))
           (else v))))
      (else v))))

(define flat-ants
  (lambda (list)
    (cond
      [(null? list) '()]
      [(pair? (car list)) `(,@(car list) ,@(flatten (cdr list)))]
      [(null? (car list)) `(,@(flatten (cdr list)))]
      [else (error 'flat-ants "Invalid Antecedents List")])))

(define find-conclusions
  (lambda (rules)
    (let ([ants (flat-ants (map (lambda (rule) (antecedents rule)) rules))]
          [conseqs (map (lambda (rule) (conseq rule)) rules)])
      (filter (lambda (conseq) (for-all (lambda (ant) (not (unify conseq ant '()))) ants)) conseqs))))

(define prove-query
  (lambda (rules sentence limit)
    (let ([store (make-store node? 'stack)]
          [init (make-node (make-state `(,sentence) '()) #f #f 0 #f)])
      (store 'in! init)
      (let try ([attempts 0])
        (if (= attempts limit)
            #f
            (let ([current (store 'out!)])
              (if (no-goals? current)
                  (begin
                    (display-explanation current) #t) ;; Good we proved the sentence
                  (let ([children (get-next-proof-nodes current rules)])
                    (if (null? children)
                        #f
                        (begin
                          (for-each (lambda (child) (store 'in! child)) children)
                          (try (add1 attempts))))))))))))

(define print-node
  (lambda (node)
    (printf "\n-------------------------------------------------------------------------------------------------------\n")
    (if (node-parent node)
        (begin
          (printf "Last Rule Fired: ~s\n" (node-lastrule node))
          (printf "Last Goal Met:   ~s\n" (node-lastgoal node))
          (printf "Substitutions:   ~s\n" (state-theta (node-state node)))))
    (printf "New Goals:       ~s\n" (state-goals (node-state node)))))    
    

(define display-explanation
  (lambda (node)
    (let ([theta (state-theta (node-state node))])
      (letrec ([trace (lambda (node)
                        (if (node-parent node)
                            (trace (node-parent node)))
                        (print-node node))])
        (printf "\nDiagnosis:       ~s\n" (replace-vars (node-lastgoal node) theta))
        (printf "Reasoning Chain:")
        (trace node)))))

(define make-rule
  (lambda (sentence)
    `(0 1 () ,sentence)))

(define diagnose
  (lambda (rules bg limit)
    (let ([rules `(,@(map make-rule bg) ,@rules)])
      (let ([conclusions (find-conclusions rules)])
        (if conclusions
            (if (for-all (lambda (conclusion) (not (prove-query rules conclusion limit))) conclusions)
                #f)
            (printf "Nothing to prove"))))))
                
      
;--------------------------------------------------------------------------------------
; Store implementation
;--------------------------------------------------------------------------------------

;; Procedure to create a general store. The type? parameter defines 
;; the object type that can be store in the store. strategy defines
;; the in/out mechanism of the store. Possible values for this
;; parameter are 'stack, 'queue, and 'bestfit. First two will
;; essentially create a stack and a queue with LIFO and FIFO strategies.
;; The third one requires an additional eval operator to be fed in to 
;; evalute the fitness of two objects in the store. The function of
;; the eval operator be to compare two objects that pass type? predicate
;; and return one of them depending on some fitness evaluation. The 
;; in strategy is irrelevant for bestfit and by default the store
;; adds new objects to the front of the old store.
;; 
;; Parameters
;;   - type?:    Predicate to test the type of objects 
;;   - strategy: Specifies the store in/out strategy. 
;;               Legal values for this are 'stack, 'queue, and 'bestfit
;;   - more:     If strategy is 'bestfit then it is mandatory to provide
;;               an evaluator function that select one from two objects
;;               of stored type based on some criteria. This evaluator
;;               function will come wrapped in the list parameter more.
(define make-store
  (lambda (type? strategy . more)
    (let ([s '()])
      (lambda fmls
        (case (car fmls)
          [(in!) (if (type? (cadr fmls))
                     (case strategy
                       [(stack bestfit) (set! s (cons (cadr fmls) s))]
                       [(queue) (set! s (append s (list (cadr fmls))))])
                     (error 'in! "invalid object type"))]
          [(out!) (if (null? s)
                      (error 'out! "empty store")
                      (if (eq? strategy 'bestfit)
                          (let ([eval (car more)])
                            ;; Apply the eval function across the store to determine the best object.
                            (let ([obj (fold-left (lambda (a x) (if a (eval a x) x)) #f s)])
                              (set! s (remq obj s))
                              obj))
                          (let ([obj (car s)])
                            (set! s (cdr s))
                            obj)))]          
          [(empty?) (null? s)]
          [(size) (length s)])))))

;; Note. It would be good if this was implemented as a priority queue using heaps for bestfit.
;--------------------------------------------------------------------------------------
                       
                    
        

                  
    


    