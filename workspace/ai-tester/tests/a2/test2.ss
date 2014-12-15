(load "../../a/a2/othello.ss")
(load "../../a/a2/a2.ss")

(define run
  (lambda (ply type)
    (let ([start (real-time)])
      (game-othello ply 'computer 'computer type)
      (printf "time: ~s" (- (real-time) start)))))