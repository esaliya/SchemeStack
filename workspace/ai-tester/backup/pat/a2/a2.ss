;;load provided othello file
(load "othello.ss")

(define-record-type state (fields position board (mutable score)))
(define max-score 250)
(define min-score -1)

;;override othello-win? function
;;checked when the board is full or when neither player can move
(define othello-win?
  (lambda (board player)
    (if (or (othello-full-board? board)
            (and (not (any-legal-moves? board player)) (not (any-legal-moves? board (opponent player)))))
        (> (count-difference board player) 0)
        #f)))

;;override othello-full-board? function
(define othello-full-board?
  (lambda (board)
    (let loop ([i 0])
      (if (= i (vector-length board))
          #t
          (if (equal? empty (vector-ref board i))
              #f
              (loop (add1 i)))))))

;;override computer-minimax-move function
(define computer-minimax-move
  (lambda (board player ply)
    (let loop ([moveslist (legal-moves board player)] [children '()])
      (if (not (null? moveslist))
          (loop (cdr moveslist) (cons (make-state (car moveslist) (board-move board player (car moveslist)) 0) children))
          (state-position (eval-best-move children 1 player ply))))))

                       
                                              
                  
                  
(define eval-best-move
  (lambda (nodes depth player ply)
    (let loop ([curnode (car nodes)])
      (let* ([maxmove (odd? depth)] [curplayer (if maxmove player (opponent player))])
        (if (= depth ply)
            (state-score-set! curnode (evaluate (state-board curnode) player))
            (begin
              (if (null? (legal-moves (state-board curnode) curplayer))
                  (state-score-set! curnode (if maxmove max-score min-score))
                  (let loop2 ([moveslist (legal-moves (state-board curnode) curplayer)] [children '()])
                    (if (not (null? moveslist))
                        (loop2 (cdr moveslist) (cons (make-state (car moveslist) (board-move (state-board curnode) curplayer (car moveslist)) 0) children))
                        (state-score-set! curnode (state-score (eval-best-move children (add1 depth) player ply))))))))
        (if maxmove
            (fold-left (lambda (a x) (if (> (state-score x) (if (number? a) a (state-score a))) x a)) min-score nodes)
            (fold-left (lambda (a x) (if (< (state-score x) (if (number? a) a (state-score a))) x a)) max-score nodes))))))

            
                  
                  
;;evaluate function. Given a board and a player, counts
;; the number of pieces belongs to the player
(define evaluate
  (lambda (board player)
    (count board player)))
            
            
        
      
