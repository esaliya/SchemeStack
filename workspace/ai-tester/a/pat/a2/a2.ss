;;load provided othello file
(load "othello.ss")

(define-record-type state (fields (mutable position) board (mutable score)))
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
          (loop (cdr moveslist) (cons (make-state (car moveslist) (board-move board player (car moveslist)) #f) children))
          (state-position (eval-best-move children 1 player ply))))))

(define eval-best-move
  (lambda (original-nodes depth player ply)
    (let loop ([nodes original-nodes])
      (if (not (null? nodes))
          (let ([curnode (car nodes)])
            (let* ([maxmove (odd? depth)] [curplayer (if maxmove player (opponent player))])
              (if (= depth ply)
                  (state-score-set! curnode ((evaluator player)(state-board curnode)))
                  (begin
                    (if (null? (legal-moves (state-board curnode) (opponent curplayer)))
                        (state-score-set! curnode (if maxmove max-score min-score))
                        (let loop2 ([moveslist (legal-moves (state-board curnode) (opponent curplayer))] [children '()])
                          (if (not (null? moveslist))
                              (loop2 (cdr moveslist) (cons (make-state (car moveslist) (board-move (state-board curnode) (opponent curplayer) (car moveslist)) #f) children))
                              (state-score-set! curnode (state-score (eval-best-move children (add1 depth) player ply)))))))))
            (loop (cdr nodes)))))
    (if (odd? depth)
        (fold-left (lambda (a x) (if (>= (state-score x) (if (number? a) a (state-score a))) x a)) min-score original-nodes)
        (fold-left (lambda (a x) (if (<= (state-score x) (if (number? a) a (state-score a))) x a)) max-score original-nodes))))

;; Creates a default state by taking just a board
(define make-default-state
  (lambda (board)
    (make-state #f board #f)))

;;overriding computer-alpha-beta-move function
(define computer-alpha-beta-move
  (lambda (board player ply)
    (let ([alpha (sub1 min-score)] [beta (add1 max-score)] [root (make-default-state board)] [e (evaluator player)])
      (state-position (eval-pruned-best root 1 player ply alpha beta e)))))

;; e is the evaluate function that estimates a value for a board for the original player
;; player is relative to the depth
(define eval-pruned-best
  (lambda (root depth player ply alpha beta e)
    (let ([maxmove (odd? depth)])
      (let loop ([nodes (get-children root player)] [alpha alpha] [beta beta] [choice #f])
        (if (not (null? nodes))
            (let ([node (car nodes)])
              (if (= depth ply)
                  (state-score-set! node (e (state-board node)))
                  (if (null? (legal-moves (state-board node) (opponent player)))
                      (state-score-set! node (if maxmove max-score min-score))
                      (state-score-set! node (state-score
                                                 (eval-pruned-best node (add1 depth) (opponent player) ply alpha beta e)))))
              (if maxmove
                  (let-values ([(alpha choice) (if (> (state-score node) alpha)
                                                   (values (state-score node) (state-position node))
                                                   (values alpha choice))])
                    (if (>= alpha beta) (make-state choice #f alpha) (loop (cdr nodes) alpha beta choice)))
                  (let-values ([(beta choice) (if (< (state-score node) beta)
                                                   (values (state-score node) (state-position node))
                                                   (values beta choice))])
                    (if (>= alpha beta) (make-state choice #f beta)  (loop (cdr nodes) alpha beta choice)))))
            (make-state choice #f (if maxmove alpha beta)))))))

     
;; Evaluator function which first binds to a particular player and returns an evaluate function.
(define evaluator
  (lambda (player)
    (lambda (board)
      (count board player))))
 
(define get-children
  (lambda (root player)
    (let loop ([moveslist (legal-moves (state-board root) player)] [children '()])
      (if (not (null? moveslist))
          (loop (cdr moveslist) (cons (make-state (car moveslist) (board-move (state-board root) player (car moveslist)) #f) children))
          children))))