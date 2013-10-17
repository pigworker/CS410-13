\section{An evaluator for well-typed programs (done by reflecting
boolean predicates)}

In the previous lecture we saw how adding booleans and conditionals to
Hutton's razor caused run-time errors, because things like adding a
boolean to a natural number doesn't really make sense.

In this lecture we will show a way to avoid these run-time errors.

The way we will do it, this time around, is to introduce types, a
typechecker (that takes an expression and a type and returns a boolean
value indicating whether the expression was of that type or not), and
then give an evaluator that given an expression, a type and a proof that
expression is of that type indeed returns something of that type --
i.e. well-typed programs cannot ``go wrong'' (as Robin Milner once
put it)!

\begin{code}
module Lec5 where

open import BasicPrelude

Val : Set
Val = Nat /+/ Two

data Expr : Set where
  val   : Val -> Expr
  plus  : Expr -> Expr -> Expr
  le    : Expr -> Expr -> Expr
  ifThenElse : Expr -> Expr -> Expr -> Expr

data Type : Set where
  NAT TWO : Type

check : Expr -> Type -> Two
check (val (inl _))          NAT  = tt
check (val (inr _))          NAT  = ff
check (val (inl _))          TWO  = ff
check (val (inr _))          TWO  = tt
check (plus e1 e2)           NAT  = check e1 NAT /\ check e2 NAT
check (plus e1 e2)           TWO  = ff
check (le e1 e2)             NAT  = ff
check (le e1 e2)             TWO  = check e1 NAT /\ check e2 NAT
check (ifThenElse ec et ef)  T    = if  check ec TWO
                                        then check et T /\ check ef T
                                        else ff

Truth : Two -> Set
Truth tt  = One
Truth ff  = Zero

invertAnd : (b1 b2 : Two) -> Truth (b1 /\ b2) -> Truth b1 /*/ Truth b2
invertAnd tt b2 p2 = <> , p2
invertAnd ff b2 pz = magic pz

invertIf : (b t f : Two) -> Truth (if b then t else f) ->
           Truth b /*/ Truth t /+/ Truth f
invertIf tt t f pt = inl (<> , pt)
invertIf ff t f pf = inr pf

evalType : Type -> Set
evalType NAT = Nat
evalType TWO = Two

eval : (e : Expr) (T : Type) -> Truth (check e T) -> evalType T
eval (val (inl x))          NAT p = x
eval (val (inl x))          TWO p = magic p
eval (val (inr x))          NAT p = magic p
eval (val (inr x))          TWO p = x
eval (plus e1 e2)           NAT p =
  let  (p1 , p2) = invertAnd (check e1 NAT) (check e2 NAT) p
  in   eval e1 NAT p1 + eval e2 NAT p2
eval (plus e1 e2)           TWO p = magic p
eval (le e1 e2)             NAT p = magic p
eval (le e1 e2)             TWO p =
  let  (p1 , p2) = invertAnd (check e1 NAT) (check e2 NAT) p
  in   eval e1 NAT p1 <= eval e2 NAT p2
eval (ifThenElse ec et ef)  T p with invertIf (check ec TWO) _ _ p
... | inr pef          = magic pef
... | inl (pec , pet)  =  let (p1 , p2) = invertAnd _ _ pet in
                          if  eval ec TWO pec
                              then eval et T p1
                              else eval ef T p2
\end{code}

\subsection{Some tests}

\begin{code}
-- 2 + 3
testExpr1 = plus (val (inl 2)) (val (inl 3))

-- \ b -> if b then 2 + 3 else 0
testExpr2 : Expr -> Expr
testExpr2 b =  ifThenElse b
               testExpr1
               (val (inl 0))

test1 : eval testExpr1 NAT _ == 5
test1 = refl

test2 : eval (testExpr2 (val (inr tt))) NAT _ == 5
test2 = refl

test3 : eval (testExpr2 (le (val (inl 2)) (val (inl 1)))) NAT _ == 0
test3 = refl
\end{code}

\paragraph{Exercise} Write some more tests (try to cover cases not
covered by above tests).

While we managed to do what we set out to do, i.e. write an evaluator
which takes well-typed expressions and does not ``go wrong'', it is still a
bit messy -- we need to manually discharge the cases where the
typechecker returns false and we also need to invert the proofs in some
of the cases.

This begs the question: can we do better?