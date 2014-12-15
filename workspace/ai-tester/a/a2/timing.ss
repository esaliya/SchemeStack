;;(load "othello.ss")

;;; Runs a timed game of Othello (Reversi).
;; 

; if a human is playing using game-human-move below, do we time them or not?
(define time-human? #f)


(define othello-timed-game
  (lambda (move-proc-black move-proc-white time)
    (let ((time-left-black time)
          (time-left-white time))
      
      ; Initialization
      ((eval move-proc-black) #t 'dummy 'dummy time-left-black time-left-white)
      ((eval move-proc-white) #t 'dummy 'dummy time-left-white time-left-black)
      
      (letrec ((play-game
                (lambda (board player)
                  (print-board board)
                  (printf "~%")
                  (if (not (any-legal-moves? board player))
                      
                      (begin
                        (printf "No legal moves for ~a, passing.~%~%" (player-name player))
                        (play-game board (opponent player)))
                      
                      (let* ([before-time (real-time)]
                             [turn-black? (eq? player black)]
                             [move ((eval (if turn-black? move-proc-black move-proc-white))
                                    #f
                                    (board-copy board)
                                    player
                                    (if turn-black? time-left-black time-left-white)
                                    (if turn-black? time-left-white time-left-black))]
                             [time-diff (cond
                                         [(and (not time-human?)
                                               turn-black? 
                                               (eq? (eval move-proc-black) game-human-move)) 
                                          0]
                                         [(and (not time-human?)
                                               (not turn-black?)
                                               (eq? (eval move-proc-white) game-human-move)) 
                                          0]
                                         [else (- (real-time) before-time)])]
                             [new-board (if (and move (game-move!? board player move))
                                            board
                                            #f)])
                        
                        (if turn-black?
                            (set! time-left-black (- time-left-black time-diff))
                            (set! time-left-white (- time-left-white time-diff)))
                        
                        (printf "Time left for ~a: ~a~%Time left for ~a: ~a~%"
                                (player-name black) time-left-black
                                (player-name white) time-left-white)
                        
                        (cond
                         [(not move)
                          (begin
                            (printf "Quitting.~%~%")
                            #f)]
                         [(not new-board)
                          (begin
                            (printf "~a disqualified for illegal move: ~a~%" (player-name player) move)
                            (printf "~a gets point.~%" (player-name (opponent player)))
                            (opponent player))]
                         
                         [(or (negative? time-left-black) (negative? time-left-white))
                          ; we can assume that the current player is the one that just ran out
                          (begin
                            (printf "~a ran out of time.~%" (player-name player))
                            (printf "~a gets point.~%" (player-name (opponent player)))
                            (opponent player))]
                         
                         [(othello-win? new-board player)
                          (begin
                            (print-board new-board)
                            (printf "~a wins.~%" (player-name player))
                            player)]
                         
                         [(othello-win? new-board (opponent player))
                          (begin
                            (print-board new-board)
                            (printf "~a wins.~%" (player-name (opponent player)))
                            (opponent player))]
                         
                         [(othello-full-board? new-board)
                          (begin
                            (print-board new-board)
                            (printf "Draw - no winners.~%")
                            0)]
                         
                         [else (play-game new-board (opponent player))]))))))
               (play-game (init-board) black)))))


; Prompts the human player to give either
; a legal move or "q" for quit.  Returns 
; #f if quitting or input move otherwise.
(define game-human-move
  (lambda (init board player time opp-time)
    (if init
        #t
        (begin
          (printf "~a, choose a move, a1-h8 (q to quit): " (player-name player))
          (let ((move (read)))
            (cond
             [(eq? move 'q) #f]
             [else move]))))))