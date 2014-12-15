;;----------------------------------
;; B551 - Assignment 1
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    sekanaya
;; Email: sekanaya@cs.indiana.edu
;;----------------------------------


;--------------------------------------------------------------------------------------
; API of the NxN Puzzle solver
;--------------------------------------------------------------------------------------

;; Note. To turn verbose goal path tracing on and off use (trace-on) and (trace-off)
;; during any time of testing

;; Creates the initial tile configuration
(define make-initial-state
  (lambda tiles
    (make-generic-state tiles)))

;; Creates the goal tile configuration
(define make-goal-state
  (lambda tiles
    (make-generic-state tiles)))

;; Default uninformed search with BFS
(define test-uninformed-search
  (lambda (init goal limit)
    (bfs-search init goal limit)))

;; Default informed search with h1 (# of bad tiles)
(define test-informed-search
  (lambda (init goal limit)
    (h1-search init goal limit)))
;--------------------------------------------------------------------------------------


;--------------------------------------------------------------------------------------
; Extra API of the 8-Puzzle solver
;--------------------------------------------------------------------------------------

;; Uninformed search2 with DFS
(define test-uninformed-search2
  (lambda (init goal limit)
    (dfs-search init goal limit)))

;; Informed search2 with h2 (Manhattan distance)
(define test-informed-search2
  (lambda (init goal limit)
    (h2-search init goal limit)))
;--------------------------------------------------------------------------------------


;--------------------------------------------------------------------------------------
; 8-Puzzle solver code
;--------------------------------------------------------------------------------------

;; DFS search. Use a stack model as the store.
(define dfs-search
  (lambda (init goal limit)
      (search init goal limit (make-store state? 'stack) #f)))

;; BFS search. Use a queue model as the store.
(define bfs-search
  (lambda (init goal limit)
      (search init goal limit (make-store state? 'queue) #f)))

;; Informed search method 1. Heuristic is the number of misaligned tiles.  
(define h1-search
  (lambda (init goal limit)
    (search init goal limit (make-store state? 'bestfit evaluate-minh) (make-hx-calc goal h1))))

;; Informed search method 2. Heuristic is the Manhattan distance of tiles.
(define h2-search
  (lambda (init goal limit)
    (search init goal limit (make-store state? 'bestfit evaluate-minh) (make-hx-calc goal h2))))

;; Generic search. The store strategy may be different
;; depending on the specific search type. The procedure works by
;; taking a state out of the store and checking it for the goal state.
;; If so trace the state for its path, else mark it as visited and 
;; explore its children. Then continue with limit reduced by one.
;; 
;; Parameters
;;   - init:    The initial state as state record type
;;   - goal:    The goal state as state record type
;;   - limit:   Maximum number of state search attempts as integer
;;   - hx:      Heuristic function (if any)  
(define search
  (lambda (init goal limit store hx)    
    (let ([visited (make-hashtable string-hash string=?)]
          [goal-key (state-key goal)])
      (store 'in! init)
      (let try ([lives limit])
        (if (zero? lives)
            (printf "\nSearch Exhausted!\n - Try increasing attempt limit")
            (let* ([current (store 'out!)] [current-key (state-key current)])
              (if (string=? goal-key current-key)
                  (begin
                    (printf "\nGoal Found!")
                    (if verbose (state-trace current))
                    (printf "\n - Solution Depth: ~s" (state-depth current))
                    (printf "\n - Total Attempts: ~s\n" (- limit lives)))
                  (begin
                    (hashtable-set! visited current-key (void))
                    (explore! current store visited hx)
                    (try (sub1 lives))))))))))

;; Given a state, generate its child states. Each child state is checked to see if 
;; already visited and ignored if so. Otherwise the parent of the child is set as 
;; the given state. The actual tile movement required to generate the new state
;; is also recorded in the child. The generated child states are stored in the store
;; of yet to be explored states. In and out strategies depend on the store
;; implementation.
;; 
;; Parameters
;;   - state:   Current state to explore as state record type
;;   - store:   The store used to keep yet to be explored states
;;   - visited: A hashtable containing the keys of already visited states
;;   - hx:      Heuristic function (if any)
(define explore!
  (lambda (state store visited hx)
    (let ([blank-idx (vector-idxq (state-v state) BLANK)])
      (let gen-child! ([moves (state-moves state blank-idx)])
        (if (not (null? moves))
            (begin
              (let ([child (state-copy state)])
                (state-move-blank! child blank-idx (car moves))
                (let ([key (state-key child)])
                  (if (not (hashtable-contains? visited key))
                      (begin
                        (state-p-set! child state)
                        (state-depth-set! child (add1 (state-depth state)))
                        (state-move-set! child (cdr (assq (car moves) opp-move-names)))
                        (if hx (state-h-set! child (hx child)))
                        (store 'in! child)))))
              (gen-child! (cdr moves))))))))
;--------------------------------------------------------------------------------------


;--------------------------------------------------------------------------------------
; Related heuristic functions
;--------------------------------------------------------------------------------------

;; Returns a heuristic calculator function for a state type record. 
;; 
;; Parameters
;;   - goal:    Goal state as state record type
;;   - hx:      Heuristic function  
(define make-hx-calc
  (lambda (goal hx)
    (let ([gv (state-v goal)])
      (lambda (current)
        (hx (state-v current) gv)))))
   
;; Heuristic function 1. h1 counts the number of bad tiles of 
;; the current values (cv) w.r.t. goal values (gv).
;; 
;; Parameters
;;   - cv:      Tile configuration as a vector for the current state
;;   - gv:      Tile configuration as a vector for the goal state
(define h1
  (lambda (cv gv)
    (let loop ([i 0] [count 0])
      (if (eq? i (vector-length gv))
          count
          (loop (add1 i) (if (eq? (vector-ref cv i) (vector-ref gv i)) count (add1 count)))))))

;; Heuristic function 2. h2 sumes Manhattan distances between 
;; current tile configuration and goal tile configuration.
;; 
;; Parameters
;;   - cv:      Tile configuration as a vector for the current state
;;   - gv:      Tile configuration as a vector for the goal state
(define h2
  (lambda (cv gv)
    (let ([n (sqrt (vector-length gv))])
      (let loop ([i 0] [count 0])
        (if (= i n)
            count
            (let ([ctx (div i n)] [cty (mod i n)] [j (vector-idxq gv (vector-ref cv i))])
              (let ([gtx (div j n)] [gty (mod j n)])
                (loop (add1 i) (+ count (abs (- gtx ctx)) (abs (- gty cty)))))))))))
                
;; Evaluator function for two states that determines the state with least heuristic value
(define evaluate-minh
  (lambda (s1 s2)
    (if (<= (state-h s1) (state-h s2)) s1 s2))) 
;--------------------------------------------------------------------------------------


;--------------------------------------------------------------------------------------
; State related functions
;--------------------------------------------------------------------------------------

;; Generic state creator
(define make-generic-state
  (lambda (tiles)
    (let ([tiles (map (lambda (tile) 
                        (if (eq? 'blank tile) BLANK tile)) 
                      tiles)])
      ;; first #f indicates no parent while second indicates no move from previous
      ;; first 0 indicates zero depth while second indicates zero heuristic value
      (make-state (list->vector tiles) #f #f 0 0))))

;; Returns the string representation of the key of the given state.
(define state-key
  (lambda (state)
    (let* ([v (state-v state)] [n (vector-length v)])
      (let gen-key ([i 0] [key ""])
        (if (= i n)
            key
            (let* ([tile (vector-ref v i)]
                   [x->string (if (symbol? tile) symbol->string number->string)])
              (gen-key (add1 i) (string-append key (x->string tile)))))))))

;; Creates a copy of the given state.
;; Default values are used for parent, move, depth, and heuristic.
(define state-copy
  (lambda (state)
    (make-state (vector-copy (state-v state)) #f #f 0 0)))

;; Changes the blank location of the state w.r.t. the given move.
(define state-move-blank!
  (lambda (state blank-idx move)
    (let* ([v (state-v state)] [n (sqrt (vector-length v))])
      (let ([swap-idx (case move
                        [(LEFT) (sub1 blank-idx)]
                        [(RIGHT) (add1 blank-idx)]
                        [(UP) (- blank-idx n)]
                        [(DOWN) (+ blank-idx n)])])
        (vector-swap! v blank-idx swap-idx)))))

;; Returns the next possible moves of the blank for the given state.
(define state-moves
  (lambda (state blank-idx)
    (let* ([n (sqrt (vector-length (state-v state)))] 
           [row (div blank-idx n)] [col (mod blank-idx n)])
      (cond
        [(= row 0) (cond
                     [(= col 0) '(RIGHT DOWN)]
                     [(= col (- n 1)) '(LEFT DOWN)]
                     [else '(LEFT RIGHT DOWN)])]
        [(= row (- n 1)) (cond
                           [(= col 0) '(RIGHT UP)]
                           [(= col (- n 1)) '(LEFT UP)]
                           [else '(LEFT RIGHT UP)])]
        [(= col 0) '(RIGHT UP DOWN)]
        [(= col (- n 1)) '(LEFT UP DOWN)]
        [else '(LEFT RIGHT UP DOWN)]))))
       
;; Prints the given state.
(define state-print
  (lambda (s)    
    (let* ([v (state-v s)] [n (sqrt (vector-length v))])
      (newline)
      (if (null? v) (printf "Improper State: null configuration")
          (do ([i 0 (add1 i)])
              ((= i (vector-length v)) (newline))
                (printf "~s " (vector-ref v i))
                (if (eq? (mod i n) (sub1 n)) (newline)))))))

;; Trace the path to the given state. 
(define state-trace
  (lambda (s)
    (cond
      [(null? s) (newline)]
      [(not (state-p s)) (state-print s)]
      [else (begin (state-trace (state-p s)) (sandwich (state-move s)) (state-print s))])))
;--------------------------------------------------------------------------------------


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
                          ;; Evaluator function to pick the best object 
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
;--------------------------------------------------------------------------------------


;--------------------------------------------------------------------------------------
; Helpers and constants
;--------------------------------------------------------------------------------------

;; Record to hold a state of the puzzle. Field v is an vector containing
;; values of the in the order nw n ne w c e sw s se. Parent of the state
;; is stored in field p. The name of the operation used to get to this 
;; state is recorded under move field. The depth at which this state is in
;; is recorded under depth field, while the heuristic value for the state is
;; recorded as h.
(define-record-type state (fields v (mutable p) (mutable move) (mutable depth) (mutable h)))

;; The move names of the actual tile, i.e. association is (blank-move . tile-move)
(define opp-move-names '((LEFT . "R") (UP . "D") (RIGHT . "L") (DOWN . "U")))

;; Representation of blank in internal states and output
(define BLANK '_)

;; Represents the boolean verbose switch
(define verbose #t)

;; Switch on the verbose trace of goal path
(define trace-on
  (lambda ()
    (set! verbose #t)))

;; Switch off the verbose trace of goal path
(define trace-off
  (lambda ()
    (set! verbose #f)))

;; Print formatter to sandwich an object between two vertical lines
;; and a down arrow head
(define sandwich 
  (lambda (jam)
    (printf "  |\n ~s\n  |\n  V\n" jam)))

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
;--------------------------------------------------------------------------------------