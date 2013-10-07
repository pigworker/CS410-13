module Lec4 where

open import BasicPrelude

Val : Set
Val = Nat /+/ Two

data Expr : Set where
  val   : Val -> Expr
  plus  : Expr -> Expr -> Expr
  le    : Expr -> Expr -> Expr
  ifThenElse : Expr -> Expr -> Expr -> Expr

Dodgy : Set -> Set
Dodgy V = One /+/ V

nat : Val -> Dodgy Nat
nat (inl x) = inr x
nat _ = inl <>

two : Val -> Dodgy Two
two (inl x) = inl <>
two (inr x) = inr x

try : {A B : Set} -> Dodgy A -> (A -> Dodgy B) -> Dodgy B
try (inl <>) f = inl <>
try (inr a) f = f a

win : {A : Set} -> A -> Dodgy A
win = inr

eval : Expr -> Dodgy Val
eval (val x) = inr x
eval (plus e1 e2) =
  try (eval e1) \ v1 ->
  try (nat v1) \ n1 ->
  try (eval e2) \ v2 ->
  try (nat v2) \ n2 ->
  win (inl (n1 + n2))
eval (le e e₁) = {!!}
eval (ifThenElse ec et ef) with eval ec 
eval (ifThenElse ec et ef) | inr (inr tt) = eval et
eval (ifThenElse ec et ef) | inr (inr ff) = eval ef
eval (ifThenElse ec et ef) | _ = inl <>
