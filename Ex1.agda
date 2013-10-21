module Ex1 where

open import BasicPrelude

{----------------------------------------------------------------------------}
{- Name:                                                                    -}
{----------------------------------------------------------------------------}

{----------------------------------------------------------------------------}
{- DEADLINE: Week 3 Thursday 10 October 23:59 (submission method to follow) -}
{----------------------------------------------------------------------------}

{-----------------------------------------------------------------------------
TOP TIP: if you have annoyingly many open goals, comment out big chunks of the
file with a multi-line comment a bit like this one.
-----------------------------------------------------------------------------}


{----------------------------------------------------------------------------}
{- 1.1: Tree Sort                                                           -}
{----------------------------------------------------------------------------}

-- 1.1.1 implement concatenation for lists

_++_ : {X : Set} -> List X -> List X -> List X
[] ++ ys = ys
(x :> xs) ++ ys = x :> (xs ++ ys)

infixr 3 _++_

-- a datatype of node-labelled binary trees is given as follows

data Tree (X : Set) : Set where
  leaf     : Tree X
  _<[_]>_  : Tree X -> X -> Tree X -> Tree X

-- 1.1.2 implement the insertion of a number into a tree, ensuring that
-- the numbers in the tree are in increasing order from left to right;
-- make sure to retain duplicates

insertTree : Nat -> Tree Nat -> Tree Nat
insertTree x leaf           = leaf <[ x ]> leaf
insertTree x (l <[ y ]> r)  with x <= y
insertTree x (l <[ y ]> r) | tt = insertTree x l <[ y ]> r
insertTree x (l <[ y ]> r) | ff = l <[ y ]> insertTree x r

-- 1.1.3 implement the function which takes the elements of a list and
-- builds an ordered tree from them, using insertTree

makeTree : List Nat -> Tree Nat
makeTree [] = leaf
makeTree (x :> xs) = insertTree x (makeTree xs)

-- 1.1.4 implement the function which flattens a tree to a list,
-- using concatenation

flatten : {X : Set} -> Tree X -> List X
flatten leaf = []
flatten (l <[ x ]> r) = flatten l ++ x :> flatten r

-- 1.1.5 using the above components, implement a sorting algorithm which
-- works by building a tree and then flattening it

treeSort : List Nat -> List Nat
treeSort = flatten o makeTree

-- 1.1.6 give a collection of unit tests which cover every program line
-- from 1.1.1 to 1.1.5

myTest : (treeSort (3 :> 1 :> 2 :> [])) == (1 :> 2 :> 3 :> [])
myTest = refl


-- 1.1.7 implement a fast version of flatten, taking an accumulating parameter,
-- never using ++. and ensuring that the law
--
--   fastFlatten t xs == flatten t ++ xs
--
-- is true; for an extra style point, ensure that the accumulating parameter
-- is never given a name in your program

fastFlatten : {X : Set} -> Tree X -> List X -> List X
fastFlatten leaf = id
fastFlatten (l <[ x ]> r) = fastFlatten l o _:>_ x o fastFlatten r

-- 1.1.8 use fastFlatten to build a fast version of tree sort

fastTreeSort : List Nat -> List Nat
fastTreeSort xs = fastFlatten (makeTree xs) []

-- 1.1.9 again, give unit tests which cover every line of code


myfastTest : (fastTreeSort (3 :> 1 :> 2 :> [])) == (1 :> 2 :> 3 :> [])
myfastTest = refl

{----------------------------------------------------------------------------}
{- 1.2: Shooting Propositional Logic Fish In A Barrel                       -}
{----------------------------------------------------------------------------}

-- 1.2.1 implement the following operations; try to use only
--   [C-c C-c] and [C-c C-a]

orCommute : {A B : Set} -> A /+/ B -> B /+/ A
orCommute (inl x) = inr x
orCommute (inr x) = inl x

orAbsorbL : {A : Set} -> Zero /+/ A -> A
orAbsorbL (inl ())
orAbsorbL (inr x) = x

orAbsorbR : {A : Set} -> A /+/ Zero -> A
orAbsorbR (inl x) = x
orAbsorbR (inr ())

orAssocR : {A B C : Set} -> (A /+/ B) /+/ C -> A /+/ (B /+/ C)
orAssocR (inl (inl x)) = inl x
orAssocR (inl (inr x)) = inr (inl x)
orAssocR (inr x) = inr (inr x)

orAssocL : {A B C : Set} -> A /+/ (B /+/ C) -> (A /+/ B) /+/ C
orAssocL (inl x) = inl (inl x)
orAssocL (inr (inl x)) = inl (inr x)
orAssocL (inr (inr x)) = inr x

-- 1.2.2 implement the following operations; try to use only
--   [C-c C-c] and [C-c C-a]

andCommute : {A B : Set} -> A /*/ B -> B /*/ A
andCommute x = outr x , outl x

andAbsorbL : {A : Set} -> A -> One /*/ A
andAbsorbL x = <> , x

andAbsorbR : {A : Set} -> A -> A /*/ One
andAbsorbR x = x , <>

andAssocR : {A B C : Set} -> (A /*/ B) /*/ C -> A /*/ (B /*/ C)
andAssocR x = outl (outl x) , outr (outl x) , outr x

andAssocL : {A B C : Set} -> A /*/ (B /*/ C) -> (A /*/ B) /*/ C
andAssocL x = (outl x , outl (outr x)) , outr (outr x)

-- how many times is [C-c C-c] really needed?

-- 1.2.3 implement the following operations; try to use only
--   [C-c C-c] and [C-c C-a]

distribute : {A B C : Set} -> A /*/ (B /+/ C) -> (A /*/ B) /+/ (A /*/ C)
distribute (outl , inl x) = inl (outl , x)
distribute (outl , inr x) = inr (outl , x)

factor : {A B C : Set} -> (A /*/ B) /+/ (A /*/ C) -> A /*/ (B /+/ C)
factor (inl x) = outl x , inl (outr x)
factor (inr x) = outl x , inr (outr x)


-- 1.2.4 try to implement the following operations; try to use only
--   [C-c C-c] and [C-c C-a]; at least one of them will prove to be
--   impossible, in which case you should comment it out and explain
--   why it's impossible

Not : Set -> Set
Not X = X -> Zero

deMorgan1 : {A B : Set} -> (Not A /+/ Not B) -> (A /*/ B) -> Zero
deMorgan1 (inl x) y = x (outl y)
deMorgan1 (inr x) y = x (outr y)

{-
deMorgan2 : {A B : Set} -> Not (A /*/ B) -> (Not A /+/ Not B)
deMorgan2 x = {!!}
-}

deMorgan3 : {A B : Set} -> (Not A /*/ Not B) -> (A /+/ B) -> Zero
deMorgan3 x (inl a) = outl x a
deMorgan3 x (inr b) = outr x b

deMorgan4 : {A B : Set} -> Not (A /+/ B) -> (Not A /*/ Not B)
deMorgan4 x = (\ a -> x (inl a)) , (\ b -> x (inr b))


-- 1.2.5 try to implement the following operations; try to use only
--   [C-c C-c] and [C-c C-a]; at least one of them will prove to be
--   impossible, in which case you should comment it out and explain
--   why it's impossible

dnegI : {X : Set} -> X -> Not (Not X)
dnegI = \ x f -> f x

{-
dnegE : {X : Set} -> Not (Not X) -> X
dnegE = {!!}
-}

neg321 : {X : Set} -> Not (Not (Not X)) -> Not X
neg321 = \ nnnx x -> nnnx (dnegI x)

{-
hamlet : {B : Set} -> B /+/ Not B
hamlet = {!!}
-}

nnHamlet : {B : Set} -> Not (Not (B /+/ Not B))
nnHamlet =  \ noham -> noham (inr (\ b -> noham (inl b)))
