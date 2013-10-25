module Lec7 where

open import BasicPrelude

Val : Set
Val = Nat

data Expr : Set where
  val   : Val -> Expr
  plus  : Expr -> Expr -> Expr

eval : Expr -> Val
eval (val x) = x
eval (plus e1 e2) = eval e1 + eval e2

data Vec (X : Set) : Nat -> Set where
  []    : Vec X zero
  _:>_  : {n : Nat} -> X -> Vec X n -> Vec X (suc n)

head : {X : Set}{n : Nat} -> Vec X (suc n) -> X
head (x :> xs) = x

data Code : Nat -> Nat -> Set where
  PUSH : {n : Nat} -> Val -> Code n (suc n)
  ADD : {n : Nat} -> Code (suc (suc n)) (suc n)
  _>>_ : {l m n : Nat} -> Code l m -> Code m n -> Code l n

infixr 4 _>>_

compile : {n : Nat} -> Expr -> Code n (suc n)
compile (val x)       = PUSH x
compile (plus e1 e2)  = compile e1 >> compile e2 >> ADD

execute : {m n : Nat} -> Code m n -> Vec Val m -> Vec Val n
execute (PUSH x) vs = x :> vs
execute ADD (y :> (x :> vs)) = (x + y) :> vs
execute (c1 >> c2) vs = execute c2 (execute c1 vs)

correct : (e : Expr){n : Nat}(xs : Vec Val n) ->
          execute (compile e) xs == (eval e :> xs)
correct (val x) xs = refl
correct (plus e1 e2) xs
  rewrite correct e1 xs | correct e2 (eval e1 :> xs) = refl