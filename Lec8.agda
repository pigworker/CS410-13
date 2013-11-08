module Lec8 where

open import BasicPrelude

Val : Set
Val = Nat /+/ Two

data Type : Set where
  NAT TWO : Type

EvalType : Type -> Set
EvalType NAT = Nat
EvalType TWO = Two

data Expr : Type -> Set where
  val   : {T : Type} -> EvalType T -> Expr T
  plus  : Expr NAT -> Expr NAT -> Expr NAT
  le    : Expr NAT -> Expr NAT -> Expr TWO
  ifThenElse : {T : Type} -> Expr TWO -> Expr T -> Expr T -> Expr T

eval : {T : Type} -> Expr T -> EvalType T
eval (val x) = x
eval (plus e1 e2) = eval e1 + eval e2
eval (le e1 e2) = eval e1 <= eval e2
eval (ifThenElse ec et ef) with eval ec
eval (ifThenElse ec et ef) | tt = eval et
eval (ifThenElse ec et ef) | ff = eval ef


data Stk : List Type -> Set where
  []    : Stk []
  _:>_  : {T : Type}{Ts : List Type}
            -> EvalType T -> Stk Ts -> Stk (T :> Ts)

data Code : List Type -> List Type -> Set where
  PUSH : {T : Type}{Ts : List Type} -> EvalType T ->
           Code Ts (T :> Ts)
  ADD : {Ts : List Type} -> Code (NAT :> NAT :> Ts) (NAT :> Ts)
  LE : {Ts : List Type} -> Code (NAT :> NAT :> Ts) (TWO :> Ts)
  _>>_ : {Rs Ss Ts : List Type} -> Code Rs Ss -> Code Ss Ts -> Code Rs Ts
  BRANCH : {Ss Ts : List Type} -> Code Ss Ts -> Code Ss Ts ->
          Code (TWO :> Ss) Ts

infixr 4 _>>_

execute : {Ss Ts : List Type} -> Code Ss Ts -> Stk Ss -> Stk Ts
execute (PUSH x) vs = x :> vs
execute ADD (y :> (x :> vs)) = (x + y) :> vs
execute LE (y :> (x :> vs)) = (x <= y) :> vs
execute (c >> c') vs = execute c' (execute c vs)
execute (BRANCH c c') (tt :> vs) = execute c vs
execute (BRANCH c c') (ff :> vs) = execute c' vs

compile : {T : Type}{Ts : List Type} -> Expr T -> Code Ts (T :> Ts)
compile (val x) = PUSH x
compile (plus e1 e2) = compile e1 >> compile e2 >> ADD
compile (le e1 e2) = compile e1 >> compile e2 >> LE
compile (ifThenElse ec et ef)
  = compile ec >> BRANCH (compile et) (compile ef)

test : Expr NAT
test = ifThenElse (le (val 5) (val 4)) (val 2) (plus (val 7) (val 9))


correct : {T : Type}(e : Expr T){Ts : List Type}
          (xs : Stk Ts) ->
          execute (compile e) xs == (eval e :> xs)
correct (val x) xs = refl
correct (plus e1 e2) xs
  rewrite correct e1 xs | correct e2 (eval e1 :> xs)= refl
correct (le e1 e2) xs
  rewrite correct e1 xs | correct e2 (eval e1 :> xs)= refl
correct (ifThenElse ec et ef) xs
  rewrite correct ec xs with eval ec
correct (ifThenElse ec et ef) xs | tt = correct et xs
correct (ifThenElse ec et ef) xs | ff = correct ef xs
