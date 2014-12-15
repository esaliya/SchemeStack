Chez Scheme Transcript [Thu Sep 02 16:16:22 2010]
> (symbol->string 'abcd)
"abcd"
> list
#<procedure list>
> (expand (list 1 23))
(1 23)
> (string-length "abc d")
5
> (string-ref 3 "abc d")
Exception in string-ref: 3 is not a string
Type (debug) to enter the debugger.
> (string-ref "abc d" 3)
#\space
> (display "hi")
hi
> (write "hi\n")
"hi\n"
> (display "hi\n")
hi
> (get-line (current-input-port))
ada
"ada"
> (define file-out (open-file-output-port "write.txt"))
> (display "some stuff" file-out)
Exception in display: #<binary output port write.txt> is not a textual output port
Type (debug) to enter the debugger.
> (define file-out (open-output-file "write.txt"))
Exception in open-output-file: failed for write.txt: file exists
Type (debug) to enter the debugger.
> (member 1 '(1 2 3))
(1 2 3)
> (memq 2 '(1 2 3))
(2 3)
> (transcript-off)
