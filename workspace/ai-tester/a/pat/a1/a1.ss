;; Kalani Ekanayake
;; kekanaya
;; Assignment 1

;;==============================================================================================
;; Constants
;;==============================================================================================
;; Record type to represent a state.
;; statevals is a vector to hold the values of tiles in the state.
;; parent is a reference to the parent state of the particular state.
;; depth indicates the depth of the state in the search tree
(define-record-type state (fields statevals (mutable parent) (mutable depth)))

;; Possible moves depending on the index of the blank. Moves are extracted by referring to the
;; moves vector with blank's position given as the index.
(define moves '#(#("R" "D") 
                 #("L" "R" "D") 
                 #("L" "D") 
                 #("U" "R" "D") 
                 #("U" "L" "R" "D") 
                 #("U" "L" "D") 
                 #("U" "R")
                 #("U" "L" "R") 
                 #("U" "L")))

;;==============================================================================================
;; API
;;==============================================================================================

;; This function creates initial state, given the 8 state values in order
(define make-initial-state
  (lambda (nw n ne w c e sw s se)
    (let ([vec (vector nw n ne w c e sw s se)])
      (make-st vec))))

;; This function creates goal state, given the 8 state values in order
(define make-goal-state
  (lambda (nw n ne w c e sw s se)
    (let ([vec (vector nw n ne w c e sw s se)])
      (make-st vec))))

(define test-uninformed-search
  (lambda (init goal limit)
    (search init goal limit #f)))

(define test-informed-search
  (lambda (init goal limit)
    (search init goal limit h1)))
;;==============================================================================================
 

;;==============================================================================================
;; State Operations
;;==============================================================================================

;; This function creates a state record, given the vector representing the state values.
;; It also replaces the symbol 'blank with a space, i.e. " ".
(define make-st
  (lambda (vec)
    (let lp ([i 0])
      (if (< i (vector-length vec))
          (let ([tmp (vector-ref vec i)])
            (cond
             [(equal? tmp 'blank) (vector-set! vec i " ")]
             [else (lp (add1 i))])))
      (make-state vec #f 0))))

;; This function prints the state to output console, when a state is given. Blank is shown
;; as a space
(define state-out
  (lambda (st)
    (newline)
    (let lp ([i 0])
      (if (< i (vector-length (state-statevals st)))
          (cond
           [(eq? (mod i 3) 2) (printf "~a " (vector-ref (state-statevals st) i))(newline) (lp (add1 i))]
           [else (printf "~a " (vector-ref (state-statevals st) i))(lp (add1 i))])))))


;; This function tests whether two given states are equal in their tile positions
(define state-equal?
  (lambda (st1 st2)
    (cond
     [(equal? (state-statevals st1) (state-statevals st2)) #t]
     [else #f])))

;This function generates a unique key for the given state. Key is generated
;concatenating the consecutive state values.
(define gen-key
  (lambda (st)
    (let ([vec (state-statevals st)] [key ""])
      (do ([i 0 (add1 i)])
          ((= i (vector-length vec)) key)
          (let ([element (vector-ref vec i)])
            (cond
              [(number? element) (set! key (string-append key (number->string element)))]
              [else (set! key (string-append key element))]))))))

;; This function trace the path to the given state. The parameter, cost indicates the
;; total cost of the path.  
(define state-path
  (lambda (st)
    (let ([parent (state-parent st)])
      (if parent (state-path parent))
      (newline)
      (state-out st))))

;; Given a state, this function generates and returns its child states as a list.
(define state-expand
  (lambda (st)
    (let ([vec (state-statevals st)])
      (let lp ([i 0])
        (if (equal? (vector-ref vec i) " ")
            (let ([nxtmoves (vector-ref moves i)])
              (let expand ([j 0] [children '()])
                (if (= j (vector-length nxtmoves))
                    children
                    (let ([child (vector-copy vec)] [nxtmove (vector-ref nxtmoves j)])
                      (cond
                        [(equal? "R" nxtmove) (swap! child i (add1 i))]
                        [(equal? "L" nxtmove) (swap! child i (sub1 i))]
                        [(equal? "U" nxtmove) (swap! child i (- i 3))]
                        [(equal? "D" nxtmove) (swap! child i (+ i 3))])
                      (expand (add1 j) (cons (make-state child st (add1 (state-depth st))) children ))))))
            (lp (add1 i)))))))
;;==============================================================================================


;;==============================================================================================
;; Generic Search
;;==============================================================================================

;; This function takes in an initial state, a goal state and a limit.
;; Then it tries to find a solution path limiting the path
;; cost to 'limit'. If the goal is found within the limit, it traces
;; back the path to goal and prints the path. If a heuristic function,
;; h is given it will be used to pick the next state to expand on.
(define search
  (lambda (initial goal limit h)
    (let ([queue `(,initial)]
          [visitedtable (make-hashtable string-hash string=?)]
          [h (if h (h goal) #f)])
      (define append!
        (lambda (states)
          (set! queue (append queue states))))
      (define next!
        (lambda ()
          (let ([next (if h (fold-left (lambda (a x) (if a (min-h-val a x h) x)) #f queue) (car queue))])
            (set! queue (remq next queue))
            next)))
      (let lp ([current (next!)] [pathcost 1])
        (if (hashtable-contains? visitedtable (gen-key current))
            (lp (next!) pathcost)
            (if (> pathcost limit)
                (printf "\nLimit exceeded.\n")
                (if (state-equal? current goal)
                    (begin 
                      (state-path current)
                      (printf "\nGoal found at depth ~a and cost ~a" (state-depth current) pathcost))
                    (begin
                      (hashtable-set! visitedtable (gen-key current) (void))
                      (append! (state-expand current))
                      (lp (next!) (add1 pathcost))))))))))
;;==============================================================================================


;;==============================================================================================
;; Heuristic Operations
;;==============================================================================================

;; Given two states and heuristic function, this function returns the state
;; with minimum heuristac value.
(define min-h-val
  (lambda (st1 st2 h)
    (if (< (h st1) (h st2))
        st1
        st2)))

;Heuristic function for wrong tiles - takes the goal and the state  in,
;compare the state against the goal, returns the number of misplaced
;tiles as the heuristic value.
(define h1
  (lambda (goal)
    (lambda (st)
      (let ([vec (state-statevals st)] [goalvec (state-statevals goal)] [count 0])
        (do ([i 0 (add1 i)])
            ((= i (vector-length vec)) count)
            (if (not (eq? (vector-ref vec i) (vector-ref goalvec i)))
                (set! count (add1 count))))))))

;Heuristic function for manhattan distance - takes the goal and the
;state in, compare the state against the goal and determines the number of
;verticle/horizontal moves should be made by tiles to form the goal state.
(define h2
  (lambda (goal)
    (lambda (st)
      (let ([vec (state-statevals st)] [goalvec (state-statevals goal)])
        (let loop ([i 0] [count 0])
          (if (= i (vector-length goalvec))
              count
              (let ([row (div i 3)] [col (mod i 3)] [j (vector-index goalvec (vector-ref vec i))])
                (let ([grow (div j 3)] [gcol (mod j 3)])
                  (loop (add1 i) (+ count (abs (- grow row)) (abs (- gcol col))))))))))))
;;==============================================================================================
    

;;==============================================================================================
;; Helpers
;;==============================================================================================

;; This function is used to swap two elements in a vector when the two indexes
;; and the vector are given             
(define swap!
  (lambda (child i j)
    (let ([tmp (vector-ref child i)])
       (vector-set! child i (vector-ref child j))
       (vector-set! child j tmp))))   




;; This function finds the vector index of an object in a given vector
;; when the object and the vector are given.
(define vector-index
  (lambda (v obj)
    (if (null? v) #f
        (let loop ([v v] [n 0])
          (if (eq? (vector-ref v n) obj) n (loop v (add1 n)))))))
;;==============================================================================================