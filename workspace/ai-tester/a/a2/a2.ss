;;----------------------------------
;; B551 - Assignment 2
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    sekanaya
;; Email: sekanaya@cs.indiana.edu
;;----------------------------------

(load "othello.ss")

; Takes a board representation (see below) and a player symbol 'black or 'white
; This version returns false if asked whether a board is a win for a player.
; This will cause problems when running the game loop so you should replace it.
(define othello-win?
  (lambda (board player)
    (let ([counts (marble-counts board player)])
      (or (and (or (and (null? (legal-moves board player)) (null? (legal-moves board (opponent player))))
                   (othello-full-board? board))
               (> (car counts) (cdr counts)))
          (= (cdr counts) 0)))))

; Takes a board representation
; This version returns false when asked if a board is full.  Likewise causes
; problems for the game loop.
(define othello-full-board?
  (lambda (board)
    (not (vector-idxq board empty))))


;; Indicats stats on or off
(define stats #f)
;; Collected stats
(define successors 0)
(define evaluated-successors 0)
(define cutoffs 0)
(define static-evaluations 0)
(define expansions 0)
(define calls 0) ;; total number of board decisions

(define initialize-stats
  (lambda ()
    (set! stats #t)
    (set! successors 0)
    (set! evaluated-successors 0)
    (set! cutoffs 0)
    (set! static-evaluations 0)
    (set! expansions 0)
    (set! calls 0)))

(define display-stats
  (lambda ()
    (if (or (not stats) (= expansions 0))
        (printf "No stats available")
        (begin
          (printf "\nTotal # of board decisions:                                      ~a\n" calls) 
          (printf "Total # expansions:                                              ~a\n\n" expansions)
          (printf "Avg. # of cutoff nodes per board decision:                       ~a\n" (div cutoffs calls))
          (printf "Avg. # of successors per board decision:                         ~a\n" (div successors calls))
          (printf "Avg. # of evaluated successors per board decision:               ~a\n\n" (div evaluated-successors calls))
          (printf "Avg. # of cutoff nodes per expansion:                            ~a\n" (div cutoffs expansions))
          (printf "Avg. # of successors per expansion (branching factor):           ~a\n" (div successors expansions))
          (printf "Avg. # of evaluated successors per expansion (branching factor): ~a\n" (div evaluated-successors expansions))))))
    

(define computer-alpha-beta-move
  (lambda (board original-player ply)
    (if stats (set! calls (add1 calls)))
    (let ([alpha (sub1 ninf)] [beta (add1 pinf)])
      (letrec ([evaluate (lambda (moves board player depth alpha beta)
                           (if stats (begin (set! expansions (add1 expansions)) (set! successors (+ (length moves) successors))))
                           (let loop ([moves moves] [alpha alpha] [beta beta] [corrmove #f])
                             (if (null? moves)
                                 (if (= depth 0)
                                     corrmove
                                     (if (even? depth) alpha beta))
                                 (let ([board (board-move board player (car moves))])
                                   (if stats (set! evaluated-successors (add1 evaluated-successors)))
                                   (let ([score (if (= depth (sub1 ply))
                                                    (begin (if stats (set! static-evaluations (add1 static-evaluations)))
                                                      (estimate board original-player))
                                                    (let ([moves (legal-moves board (opponent player))])
                                                      (if (null? moves)
                                                          (begin 
                                                            (if stats (set! static-evaluations (add1 static-evaluations)))
                                                            (if (odd? depth) ninf pinf)) ;; hard coded estimation here
                                                          (evaluate moves board (opponent player) (add1 depth) alpha beta))))])
                                     (if (even? depth) ;; Max's move
                                         (let-values ([(alpha corrmove) (if (> score alpha) (values score (car moves)) (values alpha corrmove))])
                                           (if (>= alpha beta)
                                               (begin
                                                 (if stats (set! cutoffs (+ (length (cdr moves)) cutoffs)))
                                                 (if (= depth 0) corrmove alpha)) ;; cut off - return score is alpha or corrmove if in depth 0
                                               (loop (cdr moves) alpha beta corrmove)))
                                         ;; Min's move
                                         (let-values ([(beta corrmove) (if (< score beta) (values score (car moves)) (values beta corrmove))])
                                           (if (>= alpha beta)
                                               (begin
                                                 (if stats (set! cutoffs (+ (length (cdr moves)) cutoffs)))
                                                 (if (= depth 0) corrmove beta)) ;; cut off - return score is beta or corrmove if in depth 0
                                               (loop (cdr moves) alpha beta corrmove)))))))))])
        (evaluate (legal-moves board original-player) board original-player 0 alpha beta)))))

(define computer-minimax-move
  (lambda (board original-player ply)
    (letrec ([evaluate (lambda (moves board player depth)
                         (let ([scores (map (lambda (move)
                                              (let ([board (board-move board player move)])
                                                (if (= depth (sub1 ply)) 
                                                    (estimate board original-player)
                                                    (let ([moves (legal-moves board (opponent player))])
                                                      (if (null? moves) 
                                                          (if (odd? depth) ninf pinf) ;; hard coded estimation here
                                                          (evaluate moves board (opponent player) (add1 depth)))))))
                                            moves)])
                           (let ([score (apply (if (odd? depth) min max) scores)])
                             (if (= depth 0)
                                 (let loop ([scores scores] [moves moves])
                                   (if (= (car scores) score) (car moves) (loop (cdr scores) (cdr moves))))
                                 score))))])
      (evaluate (legal-moves board original-player) board original-player 0))))


;; Just a simple estimate function
(define estimate
  (lambda (board player)
    (let ([counts (marble-counts board player)])
      (- (car counts) (cdr counts)))))
    



;--------------------------------------------------------------------------------------
; Helpers and constants
;--------------------------------------------------------------------------------------

;; ninf - negative infinity w.r.t. othello
(define ninf -65)

;; pinf - positive infinity w.r.t. othello
(define pinf 65)

;; Find the vector index of a given object using eq?
(define vector-idxq
  (lambda (v obj)
    (if (null? v) #f
        (let loop ([v v] [n 0])
          (if (= n (vector-length v)) #f
              (if (eq? (vector-ref v n) obj) n (loop v (add1 n))))))))

;; Returns the counts marbles for both players 
(define marble-counts
  (lambda (board player)
    (let loop ([i 0] [player-marbles 0] [opponent-marbles 0])
      (if (= i (vector-length board)) 
          `(,player-marbles . ,opponent-marbles)
          (let ([marble (vector-ref board i)])
            (cond
              [(eq? marble player) (loop (add1 i) (add1 player-marbles) opponent-marbles)]
              [(eq? marble empty) (loop (add1 i) player-marbles opponent-marbles)]
              [else (loop (add1 i) player-marbles (add1 opponent-marbles))]))))))
              
      
    
    
    
         