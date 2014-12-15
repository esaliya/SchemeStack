(define multi-assoc
  (lambda (x alist)
    (cond
      [(null? alist) '#f]
      [(equal? (caar alist) x) (cons (car alist) (or (multi-assoc x (cdr alist)) '()))]  
      [else (multi-assoc x (cdr alist))])))

(define filter
  (lambda (pred ls)
    (cond
      [(null? ls) '()]
      [(pred (car ls)) (cons (car ls) (filter pred (cdr ls)))]
      [else (filter pred (cdr ls))])))

(define multi-assoc2
  (lambda (x alist)
    ;; write in terms of filter
    ))

;; Homework
;; 
;; Write a procedure to do the following
;; read-csv: take filename and return a vector of vectors of strings
;; 
;; read-csv-int: same, but uses interger values
;; 
;; quicksort-vec: quick sort for vectors
;; 
;; after these, just read test.csv and sort and display
;;            



    