(define walk
  (lambda (v s)
    (cond
      ((var? v)
       (let ((a (assq v s)))
         (cond
           (a (walk (rhs a) s))
           (else v))))
      (else v))))


(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v) 
         (or 
           (occurs-check x (car v) s)
           (occurs-check x (cdr v) s)))
        (else #f)))))


 (let* ([s (make-proof-state '((screw-loose carburetor)) '())]
       [n (make-node s #f #f 0 #f)])
   (let ([nodes (get-next-proof-nodes n ruleset1)])
     (for-each (lambda (node)
                 (printf "\n********************************************************************************************************************************\n")
                 (printf "goals: ~s\n" (state-goals (node-state node)))
                 (printf "theta: ~s\n" (state-theta (node-state node)))
                 (printf "lastrule: ~s\n" (node-lastrule node))
                 (printf "lastgoal: ~s\n" (node-lastgoal node))
                 (printf "depth: ~s\n" (node-depth node))
                 (printf "parent: ~s\n" (node-parent node))
                 (printf "********************************************************************************************************************************\n")) nodes)))