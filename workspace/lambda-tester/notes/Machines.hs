{-# OPTIONS_GHC -fglasgow-exts #-}

module Machines where

import Data.List

------------------------------------------------------------------------
-- Syntax

data Exp = Var String 
         | Lam String Exp 
         | App Exp Exp 
         | Num Int
         | Uapp Uop Exp
         | Bapp Bop Exp Exp
  deriving (Eq,Show)

data Uop = Add1 | Sub1 | IsZero deriving (Eq,Show)
data Bop = Plus | Minus | Times | Exponent deriving (Eq,Show)

isValue :: Exp -> Bool
isValue (Var _) = True
isValue (Lam _ _) = True
isValue (Num _) = True
isValue _ = False

fv :: Exp -> [String]
fv (Var x) = [x]
fv (Lam x e) = delete x (fv e) 
fv (App e1 e2) = fv e1 `union` fv e2
fv (Num _) = []
fv (Uapp _ e) = fv e
fv (Bapp _ e1 e2) = fv e1 `union` fv e2

subst :: Exp -> Exp -> String -> Exp
subst (Var x) e x' | x == x' = e
                   | otherwise = Var x
subst (Lam x b) e x' | x == x' = Lam x b
                        | otherwise = 
  Lam x3 (subst (subst b (Var x3) x) e x') 
      where x3 = notin x (x' : (fv (Lam x b) ++ fv e)) 
            notin x' [] = x'
            notin x' (x:xs) | x' == x = notin (x' ++ "0") xs
                            | otherwise = notin x' xs
subst (App e1 e2) e x' = App (subst e1 e x') (subst e2 e x') 
subst (Num i) e x' = Num i
subst (Uapp u e1) e x' = Uapp u (subst e1 e x') 
subst (Bapp u e1 e2) e x' = Bapp u (subst e1 e x') (subst e2 e x') 

------------------------------------------------------------------------
-- Evaluation using standard reductions

data Answer = Const Int | Procedure 

instance Show Answer where
  show (Const i) = show i
  show Procedure = "<proc>"

data EC = Empty
        | AppLC EC Exp
        | AppRC Exp EC
        | UappC Uop EC
        | BappLC Bop EC Exp
        | BappRC Bop Exp EC
  deriving (Eq,Show)

fill :: EC -> Exp -> Exp
fill Empty e' = e'
fill (AppLC c e) e' = App (fill c e') e
fill (AppRC e c) e' = App e (fill c e') 
fill (UappC u c) e' = Uapp u (fill c e') 
fill (BappLC u c e) e' = Bapp u (fill c e') e 
fill (BappRC u e c) e' = Bapp u e (fill c e') 

decompose :: Exp -> (EC,Exp) 
decompose (Uapp u e) 
    | isValue e = (Empty, Uapp u e) 
    | otherwise = (UappC u c,e') 
      where (c,e') = decompose e
decompose (Bapp u e1 e2) 
    | isValue e1 && isValue e2 = (Empty, Bapp u e1 e2) 
    | isValue e1 = let (c,e') = decompose e2 in (BappRC u e1 c, e') 
    | otherwise = let (c,e') = decompose e1 in (BappLC u c e2, e') 
decompose (App e1 e2) 
    | isValue e1 && isValue e2 = (Empty, App e1 e2) 
    | isValue e1 = let (c,e') = decompose e2 in (AppRC e1 c, e') 
    | otherwise = let (c,e') = decompose e1 in (AppLC c e2, e') 

reduce :: Exp -> Maybe Exp
reduce e = 
  let (c,e') = decompose e 
  in do r <- case e' of 
               App (Lam x e) v -> Just $ betav e'
               _ -> delta e'
        return $ fill c r 

betav :: Exp -> Exp 
betav (App (Lam x e) v) =  subst e v x

delta :: Exp -> Maybe Exp 
delta (Uapp Add1 (Num i)) = Just $ Num (i+1) 
delta (Uapp Sub1 (Num i)) = 
    if i > 0 then Just $ Num (i-1) else Nothing
delta (Uapp IsZero (Num 0)) = Just $ Lam "x" (Lam "y" (Var "x"))
delta (Uapp IsZero (Num _)) = Just $ Lam "x" (Lam "y" (Var "y"))
delta (Bapp Plus (Num i) (Num j)) = Just $ Num (i+j) 
delta (Bapp Minus (Num i) (Num j)) = 
    if i > j then Just $ Num (i-j) else Nothing
delta (Bapp Times (Num i) (Num j)) = Just $ Num (i*j) 
delta (Bapp Exponent (Num i) (Num j)) = Just $ Num (i^j) 
delta _ = Nothing 

eval :: Exp -> Maybe Answer
eval e | isValue e = return $ toAnswer e
       | otherwise = do e' <- reduce e; eval e'

toAnswer :: Exp -> Answer
toAnswer (Num i) = Const i
toAnswer (Lam _ _) = Procedure

------------------------------------------------------------------------
-- CK machine

evalCK :: Exp -> Maybe Answer
evalCK e = do (r,[Empty]) <- ckMachine (e,[Empty]) 
              return $ toAnswer r

ckMachine :: (Exp,[EC]) -> Maybe (Exp,[EC]) 
ckMachine (App e1 e2, k) 
  | isValue e1 && isValue e2 = 
      case e1 of 
        Lam x b -> ckMachine (betav (App e1 e2), k) 
        _ -> Nothing 
  | isValue e1 = ckMachine (e2, AppRC e1 Empty : k) 
  | otherwise = ckMachine (e1, AppLC Empty e2 : k) 
ckMachine (Uapp u e, k) 
  | isValue e = do r <- delta (Uapp u e) 
                   ckMachine (r,k) 
  | otherwise = ckMachine (e, UappC u Empty : k) 
ckMachine (Bapp u e1 e2, k) 
  | isValue e1 && isValue e2 = do r <- delta (Bapp u e1 e2)
                                  ckMachine (r,k) 
  | isValue e1 = ckMachine (e2, BappRC u e1 Empty : k) 
  | otherwise = ckMachine (e1, BappLC u Empty e2 : k) 
ckMachine (e,[Empty]) | isValue e = return (e,[Empty])
                      | otherwise = Nothing
ckMachine (e,c:k) 
  | isValue e = ckMachine (fill c e, k) 
  | otherwise = Nothing


------------------------------------------------------------------------
-- Restructured CK machine

data Frame = AppLF Exp
           | AppRF Exp 
           | UappF Uop
           | BappLF Bop Exp
           | BappRF Bop Exp
  deriving Show

evalSCK :: Exp -> Maybe Answer
evalSCK e = do r <- sckMachine (e,[]) 
               return $ toAnswer r

sckMachine :: (Exp,[Frame]) -> Maybe Exp
sckMachine (e,k) = enter (e,k) 
  where enter (App e1 e2, k) = enter (e1, AppLF e2 : k)
        enter (Uapp u e, k) = enter (e, UappF u : k) 
        enter (Bapp u e1 e2, k) = enter (e1, BappLF u e2 : k) 
        enter (e,k) | isValue e = unwind (k,e) 
        unwind (AppLF e : k, v) = enter (e, AppRF v : k)
        unwind (AppRF (Lam x b) : k, v) = enter (subst b v x, k)
        unwind (UappF u : k, v) = do v' <- delta (Uapp u v) 
                                     enter (v',k)
        unwind (BappLF u e : k, v) = enter (e, BappRF u v : k)
        unwind (BappRF u v1 : k, v2) = do v' <- delta (Bapp u v1 v2)
                                          enter (v',k)
        unwind ([],v) = return v

------------------------------------------------------------------------
-- CEK machine


data RTValue = RInt Int
             | Closure String Exp Env

type Env = [(String,RTValue)]

data RTFrame = AppLRF Exp Env
             | AppRRF RTValue
             | UappRF Uop
             | BappLRF Bop Exp Env
             | BappRRF Bop RTValue

type Cont = [RTFrame]

toVal :: Exp -> Env -> Maybe RTValue
toVal (Var x) env = lookup x env
toVal (Num i) env = return $ RInt i
toVal (Lam x b) env = return $ Closure x b env

toRAnswer :: RTValue -> Answer
toRAnswer (RInt i) = Const i
toRAnswer (Closure _ _ _) = Procedure

evalCEK :: Exp -> Maybe Answer
evalCEK e = do r <- cekMachine (e,[],[]) 
               return $ toRAnswer r

cekMachine :: (Exp,Env,Cont) -> Maybe RTValue
cekMachine (e,env,k) = enter (e,env,k) 
  where enter (App e1 e2, env, k) = enter (e1, env, AppLRF e2 env : k)
        enter (Uapp u e, env, k) = enter (e, env, UappRF u : k) 
        enter (Bapp u e1 e2, env, k) = enter (e1, env, BappLRF u e2 env : k)
        enter (e,env,k) | isValue e = do v <- toVal e env
                                         unwind (k,v) 
                        | otherwise = Nothing
        unwind (AppLRF e env : k, v) = enter (e, env, AppRRF v : k)
        unwind (AppRRF (Closure x b env) : k, v) = enter (b, (x,v):env, k)
        unwind (UappRF u : k, RInt v) = do v <- delta (Uapp u (Num v))
                                           v' <- toVal v []
                                           unwind (k,v')
        unwind (BappLRF u e env : k, v) = enter (e, env, BappRRF u v : k)
        unwind (BappRRF u (RInt v1) : k, (RInt v2)) = 
            do v <- delta (Bapp u (Num v1) (Num v2))
               v' <- toVal v []
               unwind (k,v')
        unwind ([],v) = return v
        unwind _ = Nothing

------------------------------------------------------------------------
-- Macros

isZero, add1, sub1 :: Exp -> Exp 
isZero e = Uapp IsZero e
add1 e = Uapp Add1 e
sub1 e = Uapp Sub1 e 

(<+>), (<->), (<*>), (<^>) :: Exp -> Exp -> Exp
e1 <+> e2 = Bapp Plus e1 e2
e1 <-> e2 = Bapp Minus e1 e2
e1 <*> e2 = Bapp Times e1 e2
e1 <^> e2 = Bapp Exponent e1 e2

(@@) :: Exp -> Exp -> Exp
e1 @@ e2 = App e1 e2

fun :: String -> Exp -> Exp
fun x e = Lam x e

num :: Int -> Exp
num = Num

var :: String -> Exp
var = Var

ifZ :: Exp -> Exp -> Exp -> Exp
ifZ e1 e2 e3 = isZero e1 @@ (fun "_" e2) @@ (fun "_" e3) @@ (num 0)

yv = let x = var "x"
         f = var "f"
         g = var "g"
         h = fun "g" (f @@ (fun "x" (g @@ g @@ x)))
     in fun "f" (fun "x" (h @@ h @@ x))
            
------------------------------------------------------------------------
-- Examples

x = var "x"
idE = fun "x" x
e0 = idE
e1 = idE @@ (num 3)
e2 = idE @@ (num 8)
e3 = add1 (add1 (add1 (num 3)))
e4 = ifZ (num 0) e1 e2
e6 = (num 3) @@ (num 4) 

factF = let f = var "f"
            n = var "n"
        in fun "f" $
           fun "n" $
           ifZ n (num 1) (n <*> (f @@ (sub1 n)))

e7 = yv @@ factF @@ (num 5) 

------------------------------------------------------------------------
