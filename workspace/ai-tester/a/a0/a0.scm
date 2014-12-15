;;----------------------------------
;; B551 - Assignment 0
;;----------------------------------
;; Name:  Saliya Ekanayake
;; ID:    sekanaya
;; Email: sekanaya@cs.indiana.edu
;;----------------------------------

;;-------------------------------------------------------------------------------------------------------
;; Section on reading a CSV file
;;------------------------------------------------------------------------------------------------------- 

;; Reads a field in the CSV as list
(define read-field
  (lambda (port)
    (let ([c (lookahead-char port)])
      (cond
        [(or (eof-object? c) (eq? #\newline c)) '()]
        [(eq? #\, c) (get-char port) '()]
        [else (let ([c (get-char port)])
                (cons c (read-field port)))]))))

;; Reads a line and returns a list of fields each converted to proper type depending on x
(define read-line-as-x
  (lambda (port x)
    (let ([c (lookahead-char port)]
          [list->x (if (eq? x 'number) (lambda (l) (string->number (list->string l))) list->string)])
      (cond
        [(eof-object? c) '()]
        [(eq? #\newline c) (get-char port) '()]
        [else (let ([word (list->x (read-field port))])
                (cons word (read-line-as-x port x)))]))))

;; Reads an entire CSV file and returns a vector of vectors that contains fields in the proper
;; type based on x
(define read-csv-as-x
  (lambda (fname x)
    (let ([fip (open-input-file fname)])
      (letrec ([read-lines
                (lambda (port)
                  (let ([c (lookahead-char port)])
                    (cond
                      [(eof-object? c) '()]
                      [else (let ([line (list->vector (read-line-as-x port x))])
                              (cons line (read-lines port)))])))])
        (list->vector (read-lines fip))))))

;; Reads a CSV file as string
(define read-csv
  (lambda (fname)
    (read-csv-as-x fname 'string)))

;; Reads a CSV file as number
(define read-csv-num
  (lambda (fname)
    (read-csv-as-x fname 'number)))
;;-------------------------------------------------------------------------------------------------------
                              
                                   
;;-------------------------------------------------------------------------------------------------------
;; Section on Vector QuickSort
;;
;; Note. The QuickSort alogrithm was referred from Introduction to Algorithms, Cormen et al.  
;;-------------------------------------------------------------------------------------------------------                              
(define vector-quicksort!
  (lambda (v)
    (let qs ([v v] [p 0] [r (sub1 (vector-length v))])
      (if (< p r)
          (let ([q (partition-vector! v p r)])
            (qs v p (sub1 q))
            (qs v (add1 q) r))
          v))))

(define vector-swap!
  (lambda (v i j)
    (let ([temp (vector-ref v i)])
      (vector-set! v i (vector-ref v j))
      (vector-set! v j temp))))

(define partition-vector!
  (lambda (v p r)
    (let ([x (vector-ref v r)] [i (sub1 p)])
      (do ([j p (add1 j)])
          ;; test to exit the loop and expr followed before exiting
          ((eq? j r) (vector-swap! v (add1 i) r) (add1 i))
          ;; loop body
          (if (<= (vector-ref v j) x)
              (begin (set! i (add1 i)) (vector-swap! v i j)))))))

(define read-csv-and-sort
  (lambda (fname)
    (let ([fip (open-input-file fname)])
      (letrec ([read-lines
                (lambda (port)
                  (let ([c (lookahead-char port)])
                    (cond
                      [(eof-object? c) '()]
                      [else (let ([line (list->vector (read-line-as-x port 'number))])
                              (vector-quicksort! line)
                              (cons line (read-lines port)))])))])
        (list->vector (read-lines fip))))))
              
          
           
          
      