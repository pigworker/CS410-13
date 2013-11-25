module Ex4 where

open import BasicPrelude
open import FunctorKit

{- IDENTIFY YOURSELF
   Name:
-}

{- This exercise is about structure editing. The key concept is that
   of a *focused* functor.  -}

focus : Kit -> Kit
focus f = delOne f *K idK

{- delOne f means "an f with a hole instead of one element"; focus f
   means "an f with a hole, together with the element in the hole it
   amounts to "an f with a cursor position" -}

{- Meanwhile, a "zipper" is a cursor in a DATA type, consisting of the
   active subtree, together with its context, being the list of layers
   from the active position (the "hole") to the root of the data. Each
   layer's structure is computed with delOne. -}

Zipper : Kit -> Set
Zipper f = DATA f /*/ List (Fun (delOne f) (DATA f))

{- The plan is to build tools for acting on a focus f, then use them
   to act on a Zipper f -}


{- 1 Implement the (not very complicated at all) function which gets
     the element in focus from a focus. -}

here : {X : Set}(f : Kit) -> Fun (focus f) X -> X
here f xfx = {!!}


{- 2 Implement the function which rebuilds an f from a (focus f) by
     plugging the element back in its hole. -}

up : {X : Set}(f : Kit) -> Fun (focus f) X -> Fun f X
up f xfx = {!!}

{- 3 Use "up" to implement the function that navigates in a Zipper f
   all the way to the root, giving back a whole DATA f -}

toRoot : {f : Kit} -> Zipper f -> DATA f
toRoot {f} zf = {!!}


{- Wandering about in a Zipper can sometimes go wrong if you try to
   step in a direction where there's nowhere to go. So let's have
   Maybe, and its kit for failure management. -}

Maybe : Set -> Set
Maybe X = One /+/ X

fail : {X : Set} -> Maybe X
fail = inl <>

_/_ : {X : Set} -> Maybe X -> Maybe X -> Maybe X
inl <> / y = y
x / y = x

ret : {X : Set} -> X -> Maybe X
ret = inr

bind : {X Y : Set} -> Maybe X -> (X -> Maybe Y) -> Maybe Y
bind (inl <>) k = fail
bind (inr x) k = k x

{- The following is quite useful for acting on the context of a focus,
   keeping the element as it is. -}

ap1 : {A B C : Set} -> (A -> B) -> A /*/ C -> B /*/ C
ap1 f (a , c) = f a , c


{- 3 Implement the function which tries to go out *one* layer and
   fails if it is at the root already. -}

zipUp : {f : Kit} -> Zipper f -> Maybe (Zipper f)
zipUp {f} zf = {!!}


{- 4 Implement the function which takes an unfocused f and tries to focus it
   on the leftmost element position. This should fail if there are no element
   positions. -}

leftmost : {X : Set}(f : Kit) -> Fun f X -> Maybe (Fun (focus f) X)
leftmost f xf = {!!}


{- 5 Implement the function which takes a focused f and tries to move the focus
   one position further right. This should fail if there are no element
   positions to the right of the current one. -}

stepRight :  {X : Set}(f : Kit) -> Fun (focus f) X -> Maybe (Fun (focus f) X)
stepRight f xfx = {!!}


{- 6 Use your solutions to parts 4 and 5 to implement zipper navigation operations
   zipDownLeft, to visit the leftmost subtree, and zipRight, to visit the subtree to
   the right of the current position at the same level. -}

zipDownLeft zipRight : {f : Kit} -> Zipper f -> Maybe (Zipper f)

zipDownLeft {f} z = {!!}

zipRight {f} z = {!!}


{- 7 Implement the mirror image of parts 4..6. -}

rightmost : {X : Set}(f : Kit) -> Fun f X -> Maybe (Fun (focus f) X)
rightmost f xf = {!!}

stepLeft :  {X : Set}(f : Kit) -> Fun (focus f) X -> Maybe (Fun (focus f) X)
stepLeft f xfx = {!!}

zipDownRight zipLeft : {f : Kit} -> Zipper f -> Maybe (Zipper f)

zipDownRight {f} z = {!!}

zipLeft {f} z = {!!}


{- Here's a toy to help you experiment. -}

Returns : {X : Set} -> Maybe X -> Set
Returns (inl <>) = Zero
Returns (inr x) = One

returned : {X : Set}(mx : Maybe X){_ : Returns mx} -> X
returned (inl <>) {()}
returned (inr x) = x

data Journey {f : Kit}(z : Zipper f) : Set where
  stop : Journey z
  _>=>_ : (move : Zipper f -> Maybe (Zipper f)) ->
          {r : Returns (move z)} ->
          Journey (returned (move z) {r}) -> Journey z
infixr 3 _>=>_

{- 8 Construct a journey in the following tree structure which
     (a) uses all of your navigation operations
     (b) visits all of the numbered nodes
     (c) visits at least one leaf
     (d) finishes back at the root. -}

myJourney : Journey {treeK natK}
  (node'  (node'  (node' leaf' (toNatK 0) leaf')
                  (toNatK 1)
                  (node' leaf' (toNatK 2) leaf'))
          (toNatK 3) 
          (node'  ((node' leaf' (toNatK 4) leaf'))
                  (toNatK 5)
                  ((node' leaf' (toNatK 6) leaf'))) ,
  [])
myJourney = {!!}          


{- 9 Implement the operation which collects *all* the ways to go
   "down" by decorating each element with its context, thus putting
   each into focus. You will need to use the map operator with
   FunFunctor (see FunctorKit.agda) in various places. -}

down : {X : Set}(f : Kit) -> Fun f X -> Fun f (Fun (focus f) X)
down f xf = {!!}


{- 10 Implement the operation which takes *focused* data and decorates
   each element with *its own* focus, thus showing you every focus you
   can move to (with "staying put" being the focus in focus). I've
   done "staying put". Your job is to explain which "moves" are
   possible. -}

around : {X : Set}(f : Kit) -> Fun (focus f) X -> Fun (focus f) (Fun (focus f) X)

moves : {X : Set}(f : Kit) -> Fun (focus f) X -> Fun (delOne f) (Fun (focus f) X)
moves f xfx = {!!}

around f xfx = moves f xfx , xfx
