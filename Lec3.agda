module Lec3 where

open import Lec2

id : {X : Set} -> X -> X
id x = x

_o_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
(f o g) a = f (g a)

one : {Y : Set} -> Y -> List Y
one y = y :> []

_++_ : {Y : Set} -> List Y -> List Y -> List Y;   {- off to the right, ha ha -}                                                   [] ++ ys = ys;(y :> ys) ++ xs = y :> (ys ++ xs)

slowRev : {Y : Set} -> List Y -> List Y
slowRev [] = []
slowRev (y :> ys) = slowRev ys ++ one y

test' : List Nat
test' = slowRev (1 :> 2 :> 3 :> 4 :> [])

-- consider representing lists by functions which
-- prefix them

Hughes : Set -> Set
Hughes Y = List Y -> List Y

hughes2List : {Y : Set} -> Hughes Y -> List Y
hughes2List f = f []

h[] : {Y : Set} -> Hughes Y
h[] = id

hone : {Y : Set} -> Y -> Hughes Y
hone = _:>_

_h++_ : {Y : Set} -> Hughes Y -> Hughes Y -> Hughes Y
_h++_ = _o_

fastRevH : {Y : Set} -> List Y -> Hughes Y
fastRevH [] = h[]
fastRevH (y :> ys) = fastRevH ys h++ hone y

htest' : Hughes Nat
htest' = fastRevH (1 :> 2 :> 3 :> [])

fastRevH' : {Y : Set} -> List Y -> List Y -> List Y
fastRevH' [] ys = ys
fastRevH' (x :> xs) ys  = fastRevH' xs (x :> ys)

fastRev : {Y : Set} -> List Y -> List Y
fastRev = hughes2List o fastRevH



data _/+/_ (S T : Set) : Set where
  inl  : S  -> S /+/ T
  inr  : T  -> S /+/ T

_<?>_ : {S T R : Set} ->
        (S -> R) ->
        (T -> R) ->
        (S /+/ T -> R)
(f <?> g) (inl x) = f x
(f <?> g) (inr x) = g x

record _/*/_ (S T : Set) : Set where
  constructor _,_
  field
    outl  : S
    outr  : T
open _/*/_ public
infixr 4 _,_

uncurry : {S T R : Set} ->
        (S -> T -> R) ->
        (S /*/ T -> R)
uncurry f (s , t) = f s t

fact : {A B C : Set} -> A /+/ (B /*/ C) -> (A /+/ B) /*/ (A /+/ C)
fact (inl x) = (inl x) , (inl x)
fact (inr x) = inr (outl x) , inr (outr x)

exmid : {X : Set} -> X /+/ (X -> Zero)
exmid = {!!}

