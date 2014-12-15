;; Kalani Ekanayake
;; kekanaya
;; Assignment 5

;;============================================================================================== 

;;load provided help file
(load "../a5-help.ss")

;;==============================================================================================
(define ruleset1
  '(
    (1 .1 ((electrical-component ?x) (malfunctioning battery)) (left-on ?x))
    (2 .6 ((malfunctioning starter)) (malfunctioning battery))
    (3 .6 ((wont-start car)) (malfunctioning starter))
    (4 .8 ((wont-start car)) (disengaged key))
    (5 .7 ((noisy ?x)) (vibrating ?x))
    (6 .7 ((vibrating ?x)) (screw-loose ?x))))

;; record to represent a search node
(define-record-type searchnode (fields goals (mutable parent) (mutable depth) (mutable lastgoal) (mutable lastrule)))

;;utility function to check whether the sentence is a compound
(define compound?
  (lambda (x)
    (and (pair? x) (not (for-all var? x)))))
;;u
(define flatten
  (lambda (list)
    (cond
      [(null? list) '()]
      [(pair? (car list)) `(,@(car list) ,@(flatten (cdr list)))]
      [else (error 'flatten "invalid list")])))
     

;;unification function
;; takes two statements and substitution list in
;; returns accumulated substitution list if unifiable, if not #f
(define unify 
  (lambda (x y sublist)
    (cond
     [(not sublist) #f]
     [(eq? x y) sublist]
     [(var? x) (unify-var x y sublist)]
     [(var? y) (unify-var y x sublist)]
     [(and (compound? x) (compound? y)) (unify (cdr x) (cdr y) (unify (car x) (car y) sublist))]
     [(and (list? x) (list? y)) (unify (cdr x) (cdr y) (unify (car x) (car y) sublist))]
     [else #f])))

;;unification of two variables
(define unify-var
  (lambda (var val sublist)
    (cond [(assq var sublist)(unify (cdr (assq var sublist)) val sublist)]
          [(assq val sublist)(unify var (cdr (assq val sublist)) sublist)]
          [(contains? var (if (list? val) val `(,val))) #f]
          [else (cons (cons var val) sublist)])))

;;expand procedure
;;generates next child nodes, given a search node and the rule set
(define get-next-proof-nodes
  (lambda (node kb)
    (let ([f (lambda (x)
               (let ([rule (standardize-variables x)])
                  (let ([lhs (if(= (length rule) 2) '() (list-ref rule 2))] 
                        [rhs (if(= (length rule) 2) rule (list-ref rule 3))])
                    (let ([f2 (lambda (y) 
                                (let ([substitutions (unify rhs y (cadr (searchnode-goals node)))])
                                  (if substitutions
                                      (begin
                                        (make-searchnode (make-proof-state (append (remq y (car (searchnode-goals node))) lhs) substitutions)
                                                         node (add1 (searchnode-depth node))
                                                         rhs rule))
                                      #f)))])
                      (map f2 (car (searchnode-goals node)))))))])
      (flatten (map f kb)))))
                 
     
     
(define make-proof-state
  (lambda (goals sublist)
    (cons goals (list sublist))))

;;takes in a rule set, the goal to be proven and a depth limit
;; displays diagnosed path if proven
(define prove-query
  (lambda (kb sentence limit)
    (let ([queue `(,(make-searchnode (make-proof-state `(,(standardize-variables sentence)) '()) #f 0 #f #f))])
      (define cons!
        (lambda (nodes)
          (set! queue `(,@nodes ,@queue))))
      (define next!
        (lambda ()
          (let ([next (car queue)])
            (set! queue (remq next queue))
            next)))
      (let lp ([current (next!)] [pathcost 1])
        (if (> pathcost limit)
            (begin
            (printf "\nLimit exceeded.\n")
              #f)
            (if (null? (car (searchnode-goals current)))
                current
                (begin
                  (let ([children (get-next-proof-nodes current kb)])
                    (if (not (for-all not children))
                        (begin
                          (cons! (filter (lambda (x) x) children))
                          (lp (next!) (add1 pathcost)))
                        #f)))))))))


(define find-conclusions
  (lambda (ruleset)
    (let ([anticedents '()] [conseq '()] [f (lambda (x)
                                              (list-ref x 2))] [f2 (lambda (y)
                                                                     (list-ref y 3))])
      (set! anticedents (flatten (append anticedents (map f ruleset))))
      (set! conseq (append conseq (map f2 ruleset)))
      (let lp ([tests conseq] [results '()])
        (if (null? tests)
              results
            (begin 
            (let lp2([facts anticedents])
              (if (null? facts)
                  (begin
                    (set! results (cons (car tests) results))
                    (lp (cdr tests) results)
                    )
              (if (unify (car facts) (car tests) '())
                  (lp (cdr tests) results)
                  (lp2 (cdr facts)))))))))))


(define diagnose
  (lambda (ruleset bg limit)
    (let lp([conclusions (find-conclusions ruleset)])
      (if (not (null? conclusions))
      (let ([conclusion (car conclusions)] [newrules (append ruleset bg)])
        (let ([result (prove-query newrules conclusion limit)])
        (if result
            (begin
              (display-explanation result conclusion))
            #f)
        (lp (cdr conclusions))))))))
          
;;The output procedure            
(define display-explanation
  (lambda (result conclusion)
    (printf "\nDiagnosis: ~a\n\n" conclusion)
    (let lp ([pathnodes '()] [current result])
      (set! pathnodes (cons current pathnodes))
      (if (searchnode-parent current)
          (lp pathnodes (searchnode-parent current))
          (let lp2 ([nodes pathnodes])
            (if (not (null? nodes))
                (begin
                  (if (searchnode-parent (car nodes))
                      (begin
                  (printf "Last rule fired: ~a\n" (searchnode-lastrule (car nodes)))
                  (printf "Last goal met: ~a\n" (searchnode-lastgoal (car nodes))))
                      (printf ""))
                  (if (null? (car (cdr (searchnode-goals (car nodes)))))
                      (printf "")
                  (printf "substitution: ~a\n" (cdr (searchnode-goals (car nodes)))))
                  (printf "New Goals: ~a\n" (car (searchnode-goals (car nodes))))
                  (printf "--------------------------------------------------\n")
                  (lp2 (cdr nodes)))
                (printf "Diagnose complete........\n\n")))))))

            
            
