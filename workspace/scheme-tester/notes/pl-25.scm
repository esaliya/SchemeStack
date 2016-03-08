;Type Inferencing
(if (zero? 5) 6 'six)

;Function Type
(→ int int)
Thre argument function

1. Γ |- (intc n) : int

From Gamma We can derive  (intc n) is of type int; intc is a tag

2. Γ |- (intc n1) : int
3. Γ |- (intc n2) : int
---------------------
4. Γ |- (+ ,n1 ,n2) : int
Inorder to prove 4 we have to prove 1,2,3 ("the proof tree")

if condition
1. Γ |- (boolc b-exp) : bool
2. Γ |- exp1 : t
3. Γ |- exp2 : t
---------------------
4. Γ |- (if ,b-exp ,exp1 ,exp2) : t


lambda
Γ,x:tx  ;Extending the env (cons (cons x tx) Γ)
----------------------
Γ |- (λ(,x),body) : (→ ,tx ,tbody)

Variable
Γ,x:tx
----------------------
Γ |- (var ,x) : tx


application
Γ |- rator : (→ trand t)   Γ |- rand : trand
----------------------
Γ |- (app ,rator ,rand) : t
i missed getting this part right
(define !-
 (lambda (gamma exp type)
  (matche `(,exp ,type)
   (((intc ,n) int))
   (((boolc ,b) bool))
   (((not ,e) bool)
     (!- gamma e 'bool))
  (((+ ,n1 ,n2) int)
     (!- gamma n1 'int)
     (!- gamma n2 'int))
  (((if ,b-exp ,exp1 ,exp2) ,t)
     (!- gamma b-exp 'bool)
     (!- gamma exp1 t)
     (!- gamma exp2 t))
  (((lambda (,x) ,body) (-> ,t-x ,t-body))
   (!- `((,x . ,t-x) . ,bgamma) body t-body))
  (((var ,x) ,t-x)
   (lookupo x gamma t-x))
  )))

 
