;;-------------------------------------------
;; B551 - Assignment 2 - Tournament Version
;;-------------------------------------------
;; Name:  Saliya Ekanayake
;; ID:    sekanaya
;; Email: sekanaya@cs.indiana.edu
;;-------------------------------------------

(define sekanaya
  (let ()
    ;; Just a simple estimate function
    (define estimate
      (lambda (board player)
        (let ([counts (marble-counts board player)])
          (let ([score (- (car counts) (cdr counts))]
                [corners (fold-left (lambda (a x) 
                                      (cond
                                        [(eq? (board-ref board x) player) `(,(add1 (car a)) . ,(cdr a))]
                                        [(eq? (board-ref board x) (opponent player)) `(,(car a) . ,(add1 (cdr a)))]
                                        [else a])) '(0 . 0) '(0 7 56 63))]
                [edges (fold-left (lambda (a x) 
                                      (cond
                                        [(eq? (board-ref board x) player) `(,(add1 (car a)) . ,(cdr a))]
                                        [(eq? (board-ref board x) (opponent player)) `(,(car a) . ,(add1 (cdr a)))]
                                        [else a])) '(0 . 0) '(1 2 3 4 5 6 8 15 16 23 24 31 32 39 40 47 48 55 57 58 59 60 61 62))])
            (+ (* 3 (car corners)) (* -6 (cdr corners)) (* 1 (car edges)) (* -2 (cdr edges)) score 18)))))
    
    ;; ninf - negative infinity w.r.t. othello
    (define ninf -119)

    ;; pinf - positive infinity w.r.t. othello
    (define pinf 119)

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
    
    ;; Transpositions
;;    (define trans (void))
    
    (define leaves '())
    (define print-leaves
      (lambda ()
        (letrec ([print-row (lambda (board row)
                               (do ([i (* row 8) (add1 i)])
                                   ((= i (* (add1 row) 8)) (printf "  "))
                                   (let ([marble (vector-ref board i)])
                                     (printf "~a " (cond
                                                     [(eq? marble black) 'b]
                                                     [(eq? marble white) 'w]
                                                     [else '_])))))]
                 [print-rows (lambda (boards row)
                               (cond
                                 [(null? boards) (printf "\n")]
                                 [else (print-row (car boards) row) (print-rows (cdr boards) row)]))])
          (do ([i 0 (add1 i)])
              ((= i 8) (printf "\n"))
              (print-rows leaves i)))))
      
    
    ;; Alpha-Beta pruning
    (define computer-alpha-beta-move
      (lambda (board original-player ply)
        (let ([alpha (sub1 ninf)] [beta (add1 pinf)])
          (letrec ([evaluate (lambda (moves board player depth alpha beta)
                               (let loop ([moves moves] [alpha alpha] [beta beta] [corrmove #f])
                                 (if (null? moves)
                                     (if (= depth 0)
                                         corrmove
                                         (if (even? depth) alpha beta))
                                     (let ([board (board-move board player (car moves))])
                                       (let ([score (if (= depth (sub1 ply))
                                                        (begin
;;                                                          (set! leaves (append leaves `(,board)))
                                                          (estimate board original-player))
                                                        (let ([moves (legal-moves board (opponent player))])
                                                          (if (null? moves)
                                                              (if (odd? depth) ninf pinf) ;; hard coded estimation here
                                                              (evaluate moves board (opponent player) (add1 depth) alpha beta))))])
                                         (if (even? depth) ;; Max's move
                                             (let-values ([(alpha corrmove) (if (> score alpha) (values score (car moves)) (values alpha corrmove))])
                                               (if (>= alpha beta)
                                                   (if (= depth 0) corrmove alpha) ;; cut off - return score is alpha or corrmove if in depth 0
                                                   (loop (cdr moves) alpha beta corrmove))
                                               )
                                             ;; Min's move
                                             (let-values ([(beta corrmove) (if (< score beta) (values score (car moves)) (values beta corrmove))])
                                               (if (>= alpha beta)
                                                   (if (= depth 0) corrmove beta) ;; cut off - return score is beta or corrmove if in depth 0
                                                   (loop (cdr moves) alpha beta corrmove)
                                                   )
                                               )))))))])
;;            (set! leaves '())
            (let ([move (evaluate (legal-moves board original-player) board original-player 0 alpha beta)])
;;              (print-leaves)
              move)))))
    (lambda (initializing? board-state current-player remaining-time opponent-remaining-time)
      ;; Just testing without concerning time at all
      (if (not initializing?)
          
          (computer-alpha-beta-move board-state current-player 4)
;;          (begin
            ;; initializing work
            
            ;; hmm this will require more changes. let's do it later
;;            (set! trans (make-hashtable string-hash string=?)))
          ))))




