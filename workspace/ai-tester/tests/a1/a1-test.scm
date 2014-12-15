;;(define make-initial-state
;;  (lambda (nw n ne w c e sw s se)
;;    (list nw n ne w c s sw s se)))

;;(define print-state
;;  (lambda (state)
;;    (newline)
;;    (let print-tile ([state state] [n 1])
;;      (if (null? state) (newline)
;;          (begin 
;;            (printf "~s " (if (eq? 'blank (car state)) '_  (car state)))
;;            (if (zero? (mod n 3)) (newline))
;;            (print-tile (cdr state) (add1 n)))))))

;; Using this create new states by consing swapped values and rest
;;(define moves '((1 . (2 4)) (2 . (1 3 5)) (3 . (2 6))
;;                (4 . (1 5 7)) (5 . (2 4 6 8)) (6 . (3 5 9))
;;                (7 . (4 8)) (8 . (5 7 9)) (9 . (6 8))))
;;--------------------------------------------------------------------------
;; Heading with vectors
;; -------------------------------------------------------------------------

;; Helpers
;;(define vector-idxq
;;  (lambda (v obj)
;;    (if (null? v) #f
;;        (let loop ([v v] [n 0])
;;          (if (eq? (vector-ref v n) obj) n (loop v (add1 n)))))))

;;(define print-state
;;  (lambda (state)    
;;    (newline)
;;    (if (null? state) (printf "Improper State: null")
;;        (do ([n 0 (add1 n)])
;;          ((eq? n (vector-length state)) (newline))
;;          (let ([tile (vector-ref state n)])
;;            (printf "~s " (if (eq? 'blank tile) '_  tile))
;;            (if (eq? (mod n 3) 2) (newline)))))))


;; Will hold the visited state vectors
;;(define visited '())


;;(define make-initial-state
;;  (lambda (nw n ne w c e sw s se)
;;    (vector nw n ne w c e sw s se)))

               

;;(define sequel-states
;;  (lambda (state)
;;    ;; todo
;;    ))
;; 

;;--------------------------------------------------------------------------
;; Heading with records
;; -------------------------------------------------------------------------
            
;; Record to hold a state of the puzzle. Field v is an vector containing
;; values of the in the order nw n ne w c e sw s se. Parent of the state
;; is stored in field p. The name of the operation used to get to this 
;; state is recorded under op field.
(define-record-type state (fields v (mutable p) (mutable move)))

(define blank-moves '((0 . (RIGHT DOWN)) (1 . (LEFT RIGHT DOWN)) (2 . (LEFT DOWN))
                      (3 . (UP RIGHT DOWN)) (4 . (UP LEFT RIGHT DOWN)) (5 . (UP LEFT DOWN))
                      (6 . (UP RIGHT)) (7 . (UP LEFT RIGHT)) (8 . (UP LEFT))))

(define opp-move-names '((LEFT . "R") (UP . "D") (RIGHT . "L") (DOWN . "U")))

(define explore!
  (lambda (state stack visited)
    (let ([blank-idx (vector-idxq (state-v state) BLANK)])
      (let gen-child! ([moves (cdr (assoc blank-idx blank-moves))])
        (if (not (null? moves))
            (begin
              (let ([child (state-copy state)])
                (state-change! child blank-idx (car moves))
                (let ([key (state-key child)])
                  (if (not (hashtable-contains? visited key))
                      (begin
                        (state-p-set! child state)
                        (state-move-set! child (cdr (assq (car moves) opp-move-names)))
                        (stack 'push! child)))))
              (gen-child! (cdr moves))))))))

(define dfs-search
  (lambda (goal-key limit stack visited)
    (let try ([limit limit])
      (if (zero? limit)
          (printf "\nSearch Exhausted: maximum limit reached")
          (let* ([current (stack 'pop!)] [current-key (state-key current)])
            ;; A recently explored state may be equal to an already existing 
            ;; state in the stack. So when popping a state check if it's 
            ;; already visited. If so continue to next state in the stack w/
            ;; limit unchanged.
;;            (if (not (hashtable-contains visited current-key))
                (if (string=? goal-key current-key)
                    (begin
                      (printf "\nGoal Found!") (trace-me current))
                    (begin
                      (hashtable-set! visited current-key (void))
                      (explore! current stack visited)
                      (try (sub1 limit))))
                (begin (printf "*******duplicate found**********")(try limit))))))))

(define state-key
  (lambda (state)
    (let ([v (state-v state)])
      (let gen-key ([i 0] [key ""])
        (if (> i 8)
            key
            (let* ([tile (vector-ref v i)]
                   [x->string (if (symbol? tile) symbol->string number->string)])
              (gen-key (add1 i) (string-append key (x->string tile)))))))))

(define state-copy
  (lambda (state)
    (make-state (vector-copy (state-v state)) #f #f)))

(define state-change!
  (lambda (state blank-idx move)
    (let ([v (state-v state)])
      (let ([swap-idx (case move
                        [(LEFT) (sub1 blank-idx)]
                        [(RIGHT) (add1 blank-idx)]
                        [(UP) (- blank-idx 3)]
                        [(DOWN) (+ blank-idx 3)])])
        (vector-swap! v blank-idx swap-idx)))))
        
(define print-state
  (lambda (s)    
    (let ([v (state-v s)])
      (newline)
      (if (null? v) (printf "Improper State: null configuration")
          (do ([n 0 (add1 n)])
              ((eq? n (vector-length v)) (newline))
                (printf "~s " (vector-ref v n))
                (if (eq? (mod n 3) 2) (newline)))))))

(define trace-me
  (lambda (s)
    (cond
      [(null? s) (newline)]
      [(not (state-p s)) (print-state s)]
      [else (begin (trace-me (state-p s)) (sandwich (state-move s)) (print-state s))])))

      
;;-----------------------------
;; Helpers
;; ----------------------------

;; Print formatter to sandwich an object between two vertical lines
;; and a down arrow head
(define sandwich 
  (lambda (jam)
    (printf "  |\n ~s\n  |\n  V\n" jam)))

;; A simple make-stack procedure
(define make-stack
  (lambda ()
    (let ([s '()])
      (lambda fmls
        (case (car fmls)
          [(push!) (set! s (cons (cadr fmls) s))] 
          [(pop!) (if (null? s) 
                      (error 'pop! "empty stack")
                      (let ([obj (car s)])
                        (set! s (cdr s))
                        obj))]
           [(empty?) (null? s)]
           [(size) (length s)])))))

;; Find the vector index of a given object using eq?
(define vector-idxq
  (lambda (v obj)
    (if (null? v) #f
        (let loop ([v v] [n 0])
          (if (eq? (vector-ref v n) obj) n (loop v (add1 n))))))) 
         
 ;; Swap element in index i with element in index j of the given vector, v.
(define vector-swap!
  (lambda (v i j)
    (let ([temp (vector-ref v i)])
      (vector-set! v i (vector-ref v j))
      (vector-set! v j temp))))

(define make-generic-state
  (lambda (nw n ne w c e sw s se)
    (let ([tiles (map (lambda (tile) 
                        (if (eq? 'blank tile) BLANK tile)) 
                      (list nw n ne w c e sw s se))])
      (make-state (list->vector tiles) #f #f)))) ;; first #f indicates no parent while second indicates no move from previous
                      

;;-----------------------------
;; Constants
;; ----------------------------

;; Blank
(define BLANK '_)

;;-----------------------------
;; API
;; ----------------------------
(define make-initial-state
  (lambda (nw n ne w c e sw s se)
    (make-generic-state nw n ne w c e sw s se)))

(define make-goal-state
  (lambda (nw n ne w c e sw s se)
    (make-generic-state nw n ne w c e sw s se)))

(define test-uninformed-search
  (lambda (init goal limit)
    (let ([stack (make-stack)] [visited (make-hashtable string-hash string=?)])
      (stack 'push! init)
      (dfs-search (state-key goal) limit stack visited))))

;;(define test-informed-search
;;  (lambda (init goal limit)
;;    ))


  
  
