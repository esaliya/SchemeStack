;;;------------------------------------------------------------------------------
;;; othello.ss - support for an Othello (Reversi) game.
;;; 
;;; Written by Mark Wilson, 1 Oct 2008
;;; Adapted from Lisp code by Peter Norvig (Othello)
;;; Adapted from Scheme code by Matt Jadud (game-playing)
;;; 
;;; GNU Public License applies (original game-playing code was GPL)
;;;
;;; A real-life Othello board is an 8x8 grid, initially:
;;; 
;;;   a b c d e f g h
;;; 1 _ _ _ _ _ _ _ _
;;; 2 _ _ _ _ _ _ _ _
;;; 3 _ _ _ _ _ _ _ _
;;; 4 _ _ _ w b _ _ _
;;; 5 _ _ _ b w _ _ _
;;; 6 _ _ _ _ _ _ _ _ 
;;; 7 _ _ _ _ _ _ _ _
;;; 8 _ _ _ _ _ _ _ _
;;; 
;;; Each space is either empty, white, or black.
;;;
;;; According to the rules of Othello, black always moves first.
;;;------------------------------------------------------------------------------
;;; Mark says, 1 Oct 2008:  This could stand to be cleaned up a bit.
;;;  I removed some stuff from the original game-playing code that was no longer
;;;  necessary now that timed play is done with a separate game loop (see 
;;;  timing.ss), but I doubt whether the game-operation globals are strictly necessary
;;;  in light of the present timed-play mechanics, for instance.
;;;------------------------------------------------------------------------------





;; -------------------------------------------------------------------------------
;; Functions you need to rewrite
;; 
;; Don't rewrite or delete these functions in this file.  Do (load "othello.ss")
;; first thing in your "hwk3.ss" file, and redefine these functions in your file.
;; 
;; You may wish to read through the section of board-related functions below. Most
;; of the other functions in this file shouldn't be too useful in writing a B551
;; solution.
;; 
;; You may also find these global variables useful:
;; white, black, empty, all-squares
;; 
;; Note:  If you use the global variables, DON'T CHANGE THEM.
;; The game routines rely on them.
;; -------------------------------------------------------------------------------
;; 

; Takes a board representation (see below) and a player symbol 'black or 'white
; This version returns false if asked whether a board is a win for a player.
; This will cause problems when running the game loop so you should replace it.
(define othello-win?
  (lambda (board player)
    #f))

; Takes a board representation
; This version returns false when asked if a board is full.  Likewise causes
; problems for the game loop.
(define othello-full-board?
  (lambda (board)
    #f))

; Takes a board representation, a player symbol 'black or 'white,
; and a maximum ply depth for the search tree.
;
; This version of "computer-minimax-move" picks a random legal move for the given player.
; You should write a new one which calls your minimax function and returns the
; move deemed best.
(define computer-minimax-move
  (lambda (board player ply)
    (pick-random (legal-moves board player))))

; Like computer-minimax-move, but for calling your alpha-beta function
(define computer-alpha-beta-move
  (lambda (board player ply)
    (pick-random (legal-moves board player))))





;; -------------------------------------------------------------------------------
;; Misc. basic functions
;; -------------------------------------------------------------------------------
;; 

; pick a random element from a list
(define pick-random
  (lambda (ls)
    (list-ref ls (random (length ls)))))

; "or" written as a function so it can be applied to a nested list
(define or-fn
  (lambda args
    (let loop ((args args))
      (cond
       [(null? args) #f]
       [(list? (car args)) (let ((a (loop (car args))))
                             (if a
                                 a
                                 (loop (cdr args))))]
       [(car args) (car args)]
       [else (loop (cdr args))]))))

; creates a cross-product of sorts between lists of strings, appending every
; member of ls2 to every member of ls1.
; easiest way to see what this does is to look at the variable "square-names" defined below.
(define cross-string
  (lambda (ls1 ls2)
    (letrec ((cross-string-acc
              (lambda (ls1 ls2 a)
                (if (null? ls1)
                    (reverse a)
                    (let loop ((ls ls2) (a a))
                      (if (null? ls)
                          (cross-string-acc (cdr ls1) ls2 a)
                          (loop (cdr ls) (cons (string-append (car ls1) (car ls)) a))))))))
      (cross-string-acc ls1 ls2 '()))))

; crosses a list of symbols with a list of numbers, using cross-string, and converts
; the result to a list of symbols.
(define cross-symbol-number
  (lambda (ls1 ls2)
    (map string->symbol (cross-string (map symbol->string ls1) (map number->string ls2)))))






;; --------------------------------------------------------------------------------
;; Constant defintions, tests, symbolic-numeric transforms
;; --------------------------------------------------------------------------------
(define white 'white)
(define black 'black)
(define empty 'empty)

(define computer-tries 10)

; a vector of the symbols identifying each square on the board in the "column-row" format, e.g., 'h5
(define square-names (list->vector (cross-symbol-number '(a b c d e f g h) '(1 2 3 4 5 6 7 8))))
; a list of all the squares from 0 to 63
(define all-squares (iota 64))
; lists of all squares along a border
(define north-squares '(a1 b1 c1 d1 e1 f1 g1 h1))
(define south-squares '(a8 b8 c8 d8 e8 f8 g8 h8))
(define west-squares '(a1 a2 a3 a4 a5 a6 a7 a8))
(define east-squares '(h1 h2 h3 h4 h5 h6 h7 h8))
; an association list of move symbols and the values added to squares to make the moves
(define dir-moves '((nw . -9) (n . -1) (ne . 7) (e . 8) (se . 9) (s . 1) (sw . -7) (w . -8)))
; the reverse association list
(define move-dirs '((-9 . nw) (-1 . n) (7 . ne) (8 . e) (9 . se) (1 . s) (-7 . sw) (-8 . w)))
; a list of move values, northwest clockwise to due west
(define all-moves '(-9 -1 7 8 9 1 -7 -8))
; lists of all moves in a cardinal direction
(define north-moves '(nw n ne))
(define south-moves '(sw s se))
(define east-moves '(ne e se))
(define west-moves '(nw w sw))

; convert from column-row representation to an index number for a board vector
; returns -1 if invalid argument
(define h8->64
  (lambda (sym)
    (let loop ((i 0))
      (cond
       [(> i 63) -1]
       [(eq? sym (vector-ref square-names i)) i]
       [else (loop (add1 i))]))))

; convert from index number for a board vector to column-row representation
(define 64->h8
  (lambda (n)
    (vector-ref square-names n)))

; returns #t if a valid index number or column-row representation
(define valid-pos?
  (lambda (v)
    (cond
     [(symbol? v) (not (= (h8->64 v) -1))]
     [(integer? v) (and (< v 64) (>= v 0))]
     [else #f])))

; takes a direction symbol and transforms it into an additive value
(define dir->num
  (lambda (dir)
    (cdr (assq dir dir-moves))))

(define num->dir
  (lambda (dir)
    (cdr (assq dir move-dirs))))

; given a position and a direction (either numeric or symbolic), returns
; the numeric value of the new position
(define move
  (lambda (v dir)
    (let ((vsym (if (symbol? v) v (64->h8 v))) (dirsym (if (symbol? dir) dir (num->dir dir))))
      (cond
       [(and (memq vsym south-squares) (memq dirsym south-moves)) -1]
       [(and (memq vsym north-squares) (memq dirsym north-moves)) -1]
       [(and (memq vsym east-squares) (memq dirsym east-moves)) -1]
       [(and (memq vsym west-squares) (memq dirsym west-moves)) -1]
       [else
        (+ (if (symbol? v)
               (h8->64 v)
               v)
           (if (symbol? dir)
               (dir->num dir)
               dir))]))))
    
; gives the symbol for the opposing player
; throws error if bad input
(define opponent
  (lambda (sym)
    (cond
     [(eq? sym white) black]
     [(eq? sym black) white]
     [else (error 'opponent "~a is not a valid player symbol" sym)])))







;; --------------------------------------------------------------------------------
;; Board operations
;; 
;; A board is represented as a flat vector 64 positions long.  Transforms from 
;; symbolic positions to vector-ref indices are above.
;; --------------------------------------------------------------------------------
;; 


; gives the starting board for a game
(define init-board
  (lambda ()
    (let ((board (make-vector 64 empty)))
      (board-set! board 'd4 white)
      (board-set! board 'e4 black)
      (board-set! board 'd5 black)
      (board-set! board 'e5 white)
      board)))

;; ------------------------------------------------------------
;; Getting information about the board
;; ------------------------------------------------------------

; given a board and a numeric or symbolic position, returns the value
; at that position on the board
(define board-ref
  (lambda (board pos)
    (vector-ref board (if (symbol? pos) (h8->64 pos) pos))))

; given a board, returns the printf-friendly string representing
; that board
(define board->string
  (lambda (board)
    (let loop ((rowhome 0) (cur 0) (str "  a b c d e f g h~%"))
      (cond
       [(= cur -1) str]
       [else (let ((valid (valid-pos? (move cur 'e))) (start (= rowhome cur)))
               ; if moving east is valid, stick with our current row; otherwise move
               ; down one
               (loop (if valid rowhome (move rowhome 's))
                     ; if moving east is valid, do that; otherwise move down to the
                     ; new row
                     (if valid (move cur 'e) (move rowhome 's))
                     ; append a space, the current symbol, and a newline if we're
                     ; moving to a new row
                     (string-append str
                                    (if start (number->string (add1 rowhome)) "")
                                    " "
                                    (cond
                                     [(eq? (board-ref board cur) empty) "_"]
                                     [(eq? (board-ref board cur) white) "w"]
                                     [else "b"])
                                    (if valid "" (string-append "~%")) )))]))))

(define print-board
  (lambda (board)
    (printf (board->string board))))

; given a board and a player symbol, returns the total number of that
; player's pieces on the board
(define count
  (lambda (board player)
    (let loop ((pos all-squares) (a 0))
      (if (null? pos)
          a
          (loop (cdr pos) (if (eq? player (board-ref board (car pos)))
                              (add1 a)
                              a))))))

(define count-difference
  (lambda (board player)
    (- (count board player) (count board (opponent player)))))

; given a board, player symbol, numeric or symbolic position, and numeric or symbolic
; direction, returns #f if the player has no pieces in that direction from that position,
; or the numeric position of his or her first piece in that direction.
(define find-bracketing-piece
  (lambda (board player pos dir)
    (cond
     [(not (valid-pos? pos)) #f]
     [(eq? player (board-ref board pos)) pos]
     [(eq? (opponent player) (board-ref board pos)) 
      (find-bracketing-piece board 
                             player
                             (move pos dir)
                             dir)]
     [else #f])))

; given a board, player symbol, numeric or symbolic position, and numeric or symbolic
; direction, returns #f if the player would flip no opponent pieces in that direction
; by moving to the given position, or the numeric position of the player's bracketing
; piece if he or she would.
(define would-flip?
  (lambda (board player pos dir)
    (let ((adj (move pos dir)))
      (and (valid-pos? adj)
           (eq? (opponent player) (board-ref board adj))
           (find-bracketing-piece board player (move adj dir) dir)))))

; given a board, player symbol, and numeric or symbolic position, returns
; #f if the move is illegal or some numeric value if it is legal.
(define legal-move?
  (lambda (board player pos)
    (and (valid-pos? pos)
         (eq? empty (board-ref board pos))
         (apply or-fn (map (lambda (dir) (would-flip? board player pos dir)) all-moves)))))

; given a board and a player symbol, returns a list of numeric positions
; the player can legally play to
(define legal-moves
  (lambda (board player)
    (let loop ((sq all-squares) (a '()))
      (cond
       [(null? sq) a]
       [(legal-move? board player (car sq)) (loop (cdr sq) (cons (car sq) a))]
       [else (loop (cdr sq) a)]))))

; given a board and a player symbol, returns #t if the player has legal
; moves on the board and #f if not
(define any-legal-moves?
  (lambda (board player)
    (let loop ((sq all-squares))
      (cond
       [(null? sq) #f]
       [(legal-move? board player (car sq)) #t]
       [else (loop (cdr sq))]))))





;; ------------------------------------------------------------
;; Modifying the board
;; ------------------------------------------------------------

; given a board, a numeric or symbolic position, and a value, sets
; the position on the board to the new value.
(define board-set!
  (lambda (board pos v)
    (vector-set! board (if (symbol? pos) (h8->64 pos) pos) v)))

(define board-copy
  (lambda (board)
    (vector-copy board)))

; given a board, player symbol, numeric or symbolic position, and numeric
; or symbolic direction, assumes the position has just been moved to by
; the player and flips all opponent pieces in the given direction, if appropriate.
(define make-flips!
  (lambda (board player pos dir)
    (let ((bracketer (would-flip? board player pos dir)))
      (if bracketer
          (let loop ((adj (move pos dir)))
            (if (not (= bracketer adj))
                (begin
                  (board-set! board adj player)
                  (loop (move adj dir)))))))))

; given a board, player symbol, and numeric or symbolic position, moves
; the player to that location and flips opponent pieces
; modifies board in-place
; throws error if move is illegal
(define board-move!
  (lambda (board player pos)
    (if (not (legal-move? board player pos))
        (error 'board-move! "~a not a legal move for ~a" pos player)
        (begin
          (board-set! board pos player)
          (for-each (lambda (dir) (make-flips! board player pos dir)) all-moves)
          board))))

; given a board, player symbol, and numeric or symbolic position, moves
; the player to that location and flips opponent pieces without modifying
; the original board (cf. "board-move!")
; throws error if move is illegal
(define board-move
  (lambda (board player pos)
    (board-move! (board-copy board) player pos)))







;; --------------------------------------------------------------------------------
;; Game operations
;; 
;; Rely a lot on global variables to define the parameters of the game.  You
;; (the B551 student) shouldn't really need any of these when writing your functions.
;; --------------------------------------------------------------------------------
;; 

; given a player symbol, informs whether the player is human in the current global game
(define player-human?
  (lambda (player)
    (cond
     [(eq? player white) (not computer-white?)]
     [(eq? player black) (not computer-black?)]
     [else (error 'player-human? "~a is not a valid player symbol" player)])))

; given a player symbol, returns the player's name
(define player-name
  (lambda (player)
    (cond
     [(eq? player white) name-white]
     [(eq? player black) name-black]
     [else (error 'player-name "~a is not a valid player symbol" player)])))

; given a board, player, and move, destructively modifies the board, prints a message,
; and returns #t if the move is possible; leaves the board alone, prints a message,
; and returns #f otherwise
(define game-move!?
  (lambda (board player move)
    (if (legal-move? board player move)
        (begin
          (printf "~a plays to ~a~%" (player-name player) (if (symbol? move) move (64->h8 move)))
          (board-move! board player move)
          ;(print-board board)
          (printf "~%")
          #t)
        (begin
          (printf "Invalid move: ~a to ~a (perhaps computer-minimax-move is still random)~%~%"
                  (player-name player)
                  (if (symbol? move) move (64->h8 move)))
          #f))))

; calls the student-defined "computer-*-move" function repeatedly, up to a limit defined
; by the global "computer-tries", until it gets a valid move, then destructively modifies
; the board and returns #t.  If it never gets a valid move, prints a message and
; returns #f.
(define game-computer-play-h!?
  (lambda (board player ply alg)
    (let loop ((i 0))
      (if (> i computer-tries)
          (begin
            (printf "Computer player offered ~a invalid moves~%~%" computer-tries)
            #f)
          (let ((move ((cond 
                        [(eq? alg 'minimax) computer-minimax-move]
                        [(eq? alg 'alpha-beta) computer-alpha-beta-move]
                        [else (error 'game-computer-play-h?! "Invalid algorithm ~a" alg)]) (board-copy board) player ply)))
            (if (game-move!? board player move)
                #t
                (loop (add1 i))))))))

; wraps game-computer-play-h!? in a function taking 3 args
(define game-computer-play-fn
  (lambda (alg)
    (lambda (board player ply)
      (game-computer-play-h!? board player ply alg))))

; loops, printing a prompt and reading input, until the human player gives either
; a legal move or "q" for quit.  Returns #t on legal move or #f if quitting.
(define game-human-play!?
  (lambda (board player ply)
    (printf "~a, choose a move, a1-h8 (q to quit): " (player-name player))
    (let ((move (read)))
      (cond
       [(eq? move 'q) #f]
       [(game-move!? board player move) #t]
       [else (game-human-play!? board player ply)]))))

; runs the appropriate (human or computer) destructive move function
; raises error if player symbol is invalid
(define game-get-move!?
  (lambda (board player ply)
    (cond
     [(eq? player white) (play-white!? board player ply)]
     [(eq? player black) (play-black!? board player ply)]
     [else (error 'game-get-move!? "~a is not a valid player symbol" player)])))

; prints a win message for the designated player and returns #f
(define game-win-msg
  (lambda (player)
    (printf "~a wins!~%~%" (player-name player))
    #t))

; prints a message and returns #t if either player has won (according
; to the student-defined "othello-win?" function).  Returns #f if not.
(define game-check-win?
  (lambda (board)
    (cond
     [(othello-win? board black)
      (game-win-msg black)]
     [(othello-win? board white)
      (game-win-msg white)]
     [else #f])))

; returns the result of calling the student-defined "othello-full-board?"
; function -- should be #t if the board is completely full or #f else.
(define game-full-board?
  (lambda (board)
    (othello-full-board? board)))



; these constants get clobbered during gameplay
(define computer-black? #f)
(define computer-white? #t)
(define play-black!? game-human-play!?)
(define play-white!? (game-computer-play-fn 'minimax))
(define name-black "Black")
(define name-white "White")


; processing player-designation arguments to "game-main-loop".
(define game-process-player-args
  (lambda (player-black player-white alg)
    (let ((player-humanity
           (lambda (p)
             (cond
              [(eq? p 'human) #t]
              [(eq? p 'computer) #f]
              [else (error 'player-humanity
                           "player argument ~a invalid"
                           p)]))))
      (set! computer-black? (not (player-humanity player-black)))
      (set! play-black!? (if computer-black? (game-computer-play-fn alg) game-human-play!?))
      (set! computer-white? (not (player-humanity player-white)))
      (set! play-white!? (if computer-white? (game-computer-play-fn alg) game-human-play!?)))))

; the main loop of the program - returns only when game complete or human player quits.
;
; takes as arguments the ply-depth of the search, a designation for the black-chip player,
; a designation for the white-chip player, and a designation for the search algorithm.
;
; see notes on player and search designations at game-othello.
(define game-main-loop
  (lambda (ply player-black player-white alg)
    (begin
      (game-process-player-args player-black player-white alg)
      (let game-loop ((board (init-board)) (player black))
        (print-board board)
        (printf "~%")
        (cond
         [(game-check-win? board)
          (begin
            (printf "Game over.~%~%")
            (print-board board)
            (printf "~%")
            #t)]
         [(game-full-board? board)
          (begin
            (printf "No moves left.  Game tied.~%~%")
            (print-board board)
            (printf "~%")
            #t)]
         [(not (any-legal-moves? board player))
          (printf "~a has no legal moves, passing~%~%" (player-name player))
          (game-loop board (opponent player))]
         [(not (game-get-move!? board player ply))
          (printf "Quitting.~%")
          #f]
         [else (game-loop board (opponent player))])))))

; kicks the main loop of the program
;
; takes as arguments the ply-depth of the search, a designation for the black-chip player,
; and a designation for the white-chip player.
;
; player designations can be atomic:  'human or 'computer, as appropriate
; algorithm designations can be atomic: 'minimax or 'alpha-beta, as appropriate
(define game-othello
  (lambda (ply player-black player-white algorithm)
    (game-main-loop ply player-black player-white algorithm)))