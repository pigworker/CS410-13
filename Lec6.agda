module Lec6 where

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

{-
test : Expr NAT
test = ifThenElse (ifThenElse {!!} {!!} {!plus ? ?!}) {!!} {!!}
-}

eval : {T : Type} -> Expr T -> EvalType T
eval (val x) = x
eval (plus e1 e2) = eval e1 + eval e2
eval (le e1 e2) = eval e1 <= eval e2
eval (ifThenElse ec et ef) with eval ec
eval (ifThenElse ec et ef) | tt = eval et
eval (ifThenElse ec et ef) | ff = eval ef


data Raw : Set where
  val   : Val -> Raw
  plus  : Raw -> Raw -> Raw
  le    : Raw -> Raw -> Raw
  ifThenElse : Raw -> Raw -> Raw -> Raw

Maybe : Set -> Set
Maybe V = One /+/ V

win : {A : Set} -> A -> Maybe A
win = inr

oops : {A : Set} -> Maybe A
oops = inl <>

try : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
try (inl <>) f = oops
try (inr a) f = f a

-- here's check, using "with" to look at intermediate results

check : (T : Type) -> Raw -> Maybe (Expr T)
check NAT (val (inl x)) = win (val x)
check TWO (val (inl x)) = oops
check NAT (val (inr x)) = oops
check TWO (val (inr x)) = win (val x)
check NAT (plus e1 e2) with check NAT e1 | check NAT e2
check NAT (plus e1 e2) | inr e1' | inr e2' = win (plus e1' e2')
check NAT (plus e1 e2) | _ | _ = oops
check TWO (plus e1 e2) = oops
check NAT (le e1 e2) = oops
check TWO (le e1 e2) with check NAT e1 | check NAT e2
check TWO (le e1 e2) | inr e1' | inr e2' = win (le e1' e2')
check TWO (le e1 e2) | _ | _ = oops
check T (ifThenElse ec et ef) with check TWO ec | check T et | check T ef
check T (ifThenElse ec et ef) | inr ec' | inr et' | inr ef'
  = inr (ifThenElse ec' et' ef') 
check T (ifThenElse ec et ef) | _ | _ | _ = oops

-- here's the same thing, but in try...win style

check' : (T : Type) -> Raw -> Maybe (Expr T)
check' NAT (val (inl x)) = win (val x)
check' TWO (val (inl x)) = oops
check' NAT (val (inr x)) = oops
check' TWO (val (inr x)) = win (val x)
check' NAT (plus e1 e2) =
  try (check' NAT e1) \ e1' ->
  try (check' NAT e2) \ e2' ->
  win (plus e1' e2')
check' TWO (plus e1 e2) = oops
check' NAT (le e1 e2) = oops
check' TWO (le e1 e2) =
  try (check' NAT e1) \ e1' ->
  try (check' NAT e2) \ e2' ->
  win (le e1' e2')
check' T (ifThenElse ec et ef) =
  try (check' TWO ec) \ ec' ->
  try (check' T et) \ et' ->
  try (check' T ef) \ ef' ->
  win (ifThenElse ec' et' ef')

-- now here's the fancy version with the tighter spec

forget : {T : Type} -> Expr T -> Raw
forget (val {NAT} x) = val (inl x)
forget (val {TWO} x) = val (inr x)
forget (plus e1 e2) = plus (forget e1) (forget e2)
forget (le e1 e2) = le (forget e1) (forget e2)
forget (ifThenElse ec et ef) = ifThenElse (forget ec) (forget et) (forget ef)

-- This is subtly different from what I did in the lecture. 
-- In the val case, I have two hidden copies of the type (which are sure to
-- be the same): 1, the hidden argument to "forget", and 2, the hidden argument
-- to val. In the lecture, I wrote

-- forget : {T : Type} -> Expr T -> Raw
-- forget {NAT} (val x) = val (inl x)
-- forget {TWO} (val x) = val (inr x)
-- forget (plus e1 e2) = plus (forget e1) (forget e2)
-- forget (le e1 e2) = le (forget e1) (forget e2)
-- forget (ifThenElse ec et ef) = ifThenElse (forget ec) (forget et) (forget ef)

-- which made "forget" pattern match first on the type, then on the expression,
-- with the unfortunate consequence that the "ifThenElse" case does not reduce
-- unless its type matches specifically NAT or specifically TWO: a general T
-- wouldn't do, which ruined the next bit. I fixed it by reordering

-- forget : {T : Type} -> Expr T -> Raw
-- forget (plus e1 e2) = plus (forget e1) (forget e2)
-- forget (le e1 e2) = le (forget e1) (forget e2)
-- forget (ifThenElse ec et ef) = ifThenElse (forget ec) (forget et) (forget ef)
-- forget {NAT} (val x) = val (inl x)
-- forget {TWO} (val x) = val (inr x)

-- which means we only look at the type after "ifThenElse" has been dealt with.
-- But it nicer never to look at "forget"'s type argument *at all*, instead looking
-- at "val"'s type argument, because it's only in the val case that we care.

data Checking (T : Type) : Raw -> Set where
  yes : (e : Expr T) -> Checking T (forget e)
  no : {r : Raw} -> Checking T r

-- the idea is that we can only say yes if we can give the typed
-- version *of the raw original*, rather than any old thing with a type

checking : (T : Type) -> (r : Raw) -> Checking T r
checking NAT (val (inl x)) = yes (val x)
checking TWO (val (inl x)) = no 
checking NAT (val (inr x)) = no 
checking TWO (val (inr x)) = yes (val _)
checking NAT (plus e1 e2) with checking NAT e1 | checking NAT e2
checking NAT (plus .(forget e1) .(forget e2)) | yes e1 | yes e2
  = yes (plus e1 e2)
checking NAT (plus e1 e2) | _ | _ = no
checking TWO (plus e1 e2) = no 
checking NAT (le e1 e2) = no 
checking TWO (le e1 e2) with checking NAT e1 | checking NAT e2
checking TWO (le .(forget e1) .(forget e2)) | yes e1 | yes e2 = yes (le e1 e2)
checking TWO (le e1 e2) | _ | _ = no
checking T (ifThenElse ec et ef) with checking TWO ec | checking T et | checking T ef
checking T (ifThenElse .(forget ec) .(forget et) .(forget ef)) | yes ec | yes et | yes ef = yes (ifThenElse ec et ef) 
checking T (ifThenElse ec et ef) | _ | _ | _ = no

-- Crucially, in each case...
--   matching on the output of checking both
--     gives us a typed term
--     tells us that the original is given by "forget"ting that typed term
--   when we say "yes", there is only one possible typed term to give!

-- Note that when we say "yes" in the "ifThenElse" case, we know only that the
-- type is some "T", not which "T". Correspondingly, if "forget" pattern matches on
-- its hidden type argument, that will just be "T", so computation will get stuck.

-- When expressions show up in types, the way they compute is what determines
-- what things the machine sees as the same. It's sometimes important to think about
-- where pattern matching gets stuck and ask if it's getting stuck needlessly.

-- Moral: a precise spec sucks you towards the correct program, but sometimes
-- you have to debug the spec (in which case it just sucks).
