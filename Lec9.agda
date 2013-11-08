module Lec9 where

open import BasicPrelude

Le : Nat -> Nat -> Set
Le zero y = One
Le (suc x) zero = Zero
Le (suc x) (suc y) = Le x y

owoto : (x y : Nat) -> Le x y /+/ Le y x
owoto zero zero = inl <>
owoto zero (suc y) = inl <>
owoto (suc x) zero = inr <>
owoto (suc x) (suc y) = owoto x y

data LB (X : Set) : Set where
  bot : LB X
  # : X -> LB X

BLE : {X : Set}(LE : X -> X -> Set) -> LB X -> LB X -> Set
BLE LE bot y = One
BLE LE (# x) bot = Zero
BLE LE (# x) (# y) = LE x y

data OList {X : Set}(LE : X -> X -> Set)(l : LB X) : Set where
  [] : OList LE l
  _:>_ : (x : X){p : BLE LE l (# x)}(xs : OList LE (# x))   -> OList LE l

myList : OList Le bot
myList = 3 :> (6 :> (9 :> []))

insert : {l : LB Nat}(y : Nat){p : BLE Le l (# y)}(xs : OList Le l) -> OList Le l
insert y {p} [] = _:>_ y {p} []
insert y (x :> xs) with owoto y x 
insert y {p} (x :> xs) | inl p' = _:>_ y {p} (_:>_ x {p'} xs)
insert y {p} (_:>_ x {p''} xs) | inr p' = _:>_ x {p''} (insert y {p'} xs)
