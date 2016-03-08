(load "timing.ss")

;; Runs a tournament from a list of players

;; Each player collects points
;; by playing every other player once as 'black and once as 'white during the player's
;; run.  The number of points for that player is equal to the number of
;; games that player wins during her run.  The opponent does not win any
;; points even if she wins during another player's run.
;; 

(define match-time 64000)
(define match-bottom-time 125)
(define players '(mw54))
(define player-names '("Mark"))
(define opponents '(mw54))

;; loads player source code
(define load-player-procs
  (lambda (players)
    (if (null? players) 'done
        (begin
          (load (string-append (symbol->string (car players)) ".ss"))
          ((eval (car players)) #t 'dummy 'dummy 'dummy 'dummy) 
          (load-player-procs (cdr players))))))
(load-player-procs players)

;; run tournament
(define tourn
  (lambda (player-list player-names all-scores)
    (if (null? player-list)
        (display all-scores)
        (let* ((cur-player-name (car player-names))
              (cur-player (car player-list))
              (points 0)
              (new-scores (cons (list cur-player-name (play-all cur-player points opponents))
                all-scores)))
          (tourn (cdr player-list) (cdr player-names) new-scores)))))
;(tourn players player-names '())

;; one vs. the rest
(define play-all
  (lambda (cur-player points opponent-list)
    (if (null? opponent-list)
        points
        (let ((opponent (car opponent-list)))
          (if (not (equal? opponent cur-player))
              (play-all cur-player
                        (+ points (play-one cur-player opponent))
                        (cdr opponent-list))
              (play-all cur-player points (cdr opponent-list)))))))



;; one vs. one, cutting time in half and trying again if
;; two tied games or one game to each player
(define play-one
  (lambda (cur-player opponent)
    (let play-loop ((time match-time))
      (let* ((b-match (othello-timed-game cur-player opponent time))
             (w-match (othello-timed-game opponent cur-player time))
             (halftime (/ time 2))
             (result (+ (get-w-points w-match) (get-b-points b-match))))
        (cond
         [(and (integer? b-match) (integer? w-match)) 
          (if (<= halftime match-bottom-time)
              (begin
                (printf "Two tied games but lower time limit reached, allowing tie.~%~%")
                result)
              (begin
                (printf "Two tied games, replaying with time limit ~a.~%~%" halftime)
                (play-loop halftime)))]
         [(= 1 result) 
          (if (<= halftime match-bottom-time)
              (begin
                (printf "One game to each player, but lower time limit reached, allowing tie.~%~%")
                result)
              (begin
                (printf "One game to each player, replaying with time limit ~a.~%~%" halftime)
                (play-loop halftime)))]
         [else result])))))

(define get-b-points
  (lambda (b-match) (if (equal? b-match black) 1 0)))
(define get-w-points
  (lambda (w-match) (if (equal? w-match white) 1 0)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; allows players to play themselves
(define tourn-including-self
  (lambda (player-list player-names all-scores)
    (if (null? player-list)
        (display all-scores)
        (let* ((cur-player-name (car player-names))
              (cur-player (car player-list))
              (points 0)
              (new-scores (cons (list cur-player-name (play-all-including-self cur-player points opponents))
                all-scores)))
          (tourn (cdr player-list) (cdr player-names) new-scores)))))

;; one vs. the rest, allowing cur-player to play itself
(define play-all-including-self
  (lambda (cur-player points opponent-list)
    (if (null? opponent-list)
        points
        (let ((opponent (car opponent-list)))
          (play-all cur-player
                    (+ points (play-one cur-player opponent))
                    (cdr opponent-list))))))