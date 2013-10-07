module Lec2 where

-- Oh, you made it! Well done! This line is a comment.

-- In the beginning, Agda knows nothing, but we can teach it about numbers.

data Nat : Set where
  zero  :  Nat
  suc   :  Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

-- Now we can say how to add numbers.

_+_ : Nat -> Nat -> Nat
zero + n = n
suc m + n = suc (m + n)

-- Now we can try adding some numbers.

four : Nat
four = (suc (suc zero)) + (suc (suc zero))

-- To make it go, select "Evaluate term to normal form" from the
-- Agda menu, then type "four", without the quotes, and press return.

-- Hopefully, you should get a response
--   suc (suc (suc (suc zero)))

data Zero : Set where

magic : {X : Set} -> Zero -> X
magic ()

record One : Set where
  constructor <>

it : One
it = _

data Two : Set where
  tt ff : Two

_<=_ : Nat -> Nat -> Two
zero <= y = tt
suc x <= zero = ff
suc x <= suc y = x <= y

data List (X : Set) : Set where
  [] : List X
  _:>_ : X -> List X -> List X

infixr 3 _:>_

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

insertionSort : List Nat -> List Nat

insertList : Nat -> List Nat -> List Nat

insertionSort [] = []
insertionSort (x :> xs) = insertList x (insertionSort xs)

insertList y [] = y :> []
insertList y (x :> xs) with y <= x
insertList y (x :> xs) | tt = y :> x :> xs
insertList y (x :> xs) | ff = x :> insertList y xs

test : insertionSort (5 :> 3 :> 1 :> 4 :> 2 :> []) ==
         (1 :> 2 :> 3 :> 4 :> 5 :> [])
test = refl
