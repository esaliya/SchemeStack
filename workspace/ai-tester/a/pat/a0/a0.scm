;; Kalani Ekanayake
;; kekanaya
;; Assignment 0

;;This procedure reads characters till it meets a comma or newline 
;; and makes a character list and converts it to a string, when an open port is given
(define read-word
  (lambda (p)
    (list->string
     (let f ([c (read-char p)])
       (cond
        [(eof-object? c) '()]
        [(eq? #\newline c) '()]
        [(not(eq? #\, c)) (cons c (f (read-char p)))]
        [else '()])))))


;;This procedure takes a file name in, opens a port, get line by line and calls the procedure "read-word" to
;; read the words separated by commas from the file, constructs a vector containing vectors 
;; containing those words in each line
(define read-csv
  (lambda (fname)
    (let ([fip (open-input-file fname)])
      (list->vector
        (let linelp ([line (get-line fip)])
          (cond
           [(eof-object? line) '()]
           [else (cons
                  (let ([lineprt (open-string-input-port line)])
                    (list->vector
                    (let mklist ([word (read-word lineprt)])
                      (cond
                       [(not(equal? "" word)) (cons word (mklist (read-word lineprt)))]
                       [else '()])))) (linelp (get-line fip)))]))))))

;;This procedure does the same task as the read-csv but storing numerical values instead of strings.
(define read-csv-num
  (lambda (fname)
    (let ([fip (open-input-file fname)])
      (list->vector
        (let linelp ([line (get-line fip)])
          (cond
           [(eof-object? line) '()]
           [else (cons
                  (let ([lineprt (open-string-input-port line)])
                    (list->vector
                    (let mklist ([word (read-word lineprt)])
                      (cond
                       [(not(equal? "" word)) (cons (string->number word) (mklist (read-word lineprt)))]
                       [else '()])))) (linelp (get-line fip)))]))))))

;;------------------------------------------------------------------------------------------------
;; Vector quick sort section
;;
(define swap
  (lambda (vec i j)
    (let ([tmp (vector-ref vec i)])
       (vector-set! vec i (vector-ref vec j))
       (vector-set! vec j tmp))))

(define partition
  (lambda (vec sindex eindex)
    (let ([pivot (vector-ref vec eindex)] [i (- sindex 1)])
      (do ([j sindex (+ j 1)])
        ((= j eindex) (swap vec (+ i 1) eindex) (+ i 1))
        (cond
         [(>= pivot (vector-ref vec j)) (set! i (+ i 1)) (swap vec i j)])))))

(define vector-quicksort!
  (lambda (vec)
    (let partitionlp ([sindex 0] [eindex (- (vector-length vec) 1)])
      (if (< sindex eindex)
          (let ([pindex (partition vec sindex eindex)])
            (partitionlp sindex  (- pindex 1))
            (partitionlp (+ pindex 1) eindex))
          vec))))

       
;;----------------------------------------------------------------------------------------------------
;;this script sorts each line in data.csv
;; 
(let ([numvec (read-csv-num "data.csv")])
  (display "sorting...\n")
  (do ([i 0 (+ i 1)])
  ((>= i (vector-length numvec)) (display "done."))
  (display (vector-quicksort! (vector-ref numvec i)))
  (display "\n")))

      

    
 