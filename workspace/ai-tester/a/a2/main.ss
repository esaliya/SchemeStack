;; My own main program for tournament
(load "othello.ss")
(load "timing.ss")
(load "sekanaya.ss")

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

(define vector-idxq
      (lambda (v obj)
        (if (null? v) #f
            (let loop ([v v] [n 0])
              (if (= n (vector-length v)) #f
                  (if (eq? (vector-ref v n) obj) n (loop v (add1 n))))))))

(othello-timed-game 'sekanaya 'game-human-move 64000) 