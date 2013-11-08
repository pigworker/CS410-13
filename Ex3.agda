module Ex3 where

{- Identify yourself

   Name:

-}

{- This exercise is about ordered data structures, involving two variations
   on the search trees. -}

open import BasicPrelude

{- To keep the development clean, I suggest that we use the module system.
   Agda modules can have parameters, so we can parametrize the whole development
   by... -}

module OTreeSort
         {X : Set}                                  -- a set of elements
         {Le : X -> X -> Set}                       -- an order relation on them
         (owoto : (x y : X) -> Le x y /+/ Le y x)   -- a function which orders
         where

{- Part A: Tree Sort -}

{- So that we can represent bounds cleanly, let's extend X with a bottom element
   and a top element. Everything should be between bottom and top. -}

  data BT : Set where
    bot : BT
    # : X -> BT
    top : BT

{- Define the ordering relation on BT. -}

  BTLE : BT -> BT -> Set
  BTLE a b = {!!}

{- Let's define binary search trees with elements between bounds. -}

  data OTree (l u : BT) : Set where
    leaf : {{_ : BTLE l u}} -> OTree l u
    node : (x : X) -> OTree l (# x) -> OTree (# x) u -> OTree l u

{- The "leaf" constructor takes as an implicit argument the proof that the
   lower bound is below the upper bound. The doubled braces tell Agda to
   infer its value by searching the context for something of the right type.
   We should it ensure that there's something to find!
   The "node" constructor just uses the node value to bound the subtrees.
   If you think about binary trees, you'll notice that there is a leaf
   left of the leftmost node, between each node, and right of the rightmost
   node, so that we have a sequence of less-or-equal evidence from the
   lower bound, through each element, to the upper bound.  -}

{- Now let's define what it means to be an element of a bounded interval. -}

  record Interval (l u : BT) : Set where
    constructor [_]
    field
      val : X
      {{below}} : BTLE l (# val)    -- again, the doubled braces mean these
      {{above}} : BTLE (# val) u    -- fields are to be found in the context

{- Now your turn. Define the function which takes an interval and a tree
   with common bounds, then delivers the result of inserting the element
   from the interval into the tree. -}

  insertOTree : {l u : BT} -> Interval l u -> OTree l u -> OTree l u
  insertOTree ilu tlu = {!!}

{- Show how to build a tree from the elements of a list. -}

  makeOTree : List X -> OTree bot top
  makeOTree xs = {!!}

{- Now that we have trees, let's flatten them to ordered lists. Unlike
   in lectures, but as for trees and intervals, let's have both lower and
   upper bounds. I've left out the ordering evidence. You put it in,
   using doubled braces. Ensure that, as with trees, there is always a
   sequence of less-or-equal evidence from the lower bound, through each
   element, to the upper bound. -}

  data OList (l u : BT) : Set where
    [] : OList l u                             -- what evidence is needed?
    _:>_ : (x : X)(xs : OList (# x) u) ->      -- what evidence is needed?
           OList l u

{- Now implement the flattening function. You may have to think about what
   other functions you need in order to do so. In particular, you may find
   that concatenation for "OList" is tricky to define, but you may also find
   that concatenation isn't exactly what you need to define. -}


  flattenOTree : {l u : BT} -> OTree l u -> OList l u
  flattenOTree t = {!!}

  treeSort : List X -> OList bot top
  treeSort = flattenOTree o makeOTree

{- See the bottom of the file for testing kit. -}

{- Part B 2-3-Tree Sort -}

{- A 2-3-Tree is a variant on a binary tree with two important differences.
  (1) it's *balanced*, so that the root is the same distance above all the
        trees; we call that distance the "height", and we index the type
        by height in order to ensure balancing
  (2) as well as the usual 2-nodes, with one value in the node and 2 subtrees,
        we have 3-nodes, with two values in the node and 3 subtrees, where
        the middle subtree's elements should be *between* the two node values

As before, I've left it to you to put the ordering evidence somewhere sensible.
-}

  data T23 (l u : BT) : Nat -> Set where -- this needs ordering evidence
    leaf : T23 l u zero
    node2 : {n : Nat}(x : X) -> T23 l (# x) n -> T23 (# x) u n ->
              T23 l u (suc n)
    node3 : {n : Nat}(x y : X) ->
            T23 l (# x) n -> T23 (# x) (# y) n -> T23 (# y) u n ->
              T23 l u (suc n)

{- When you insert into a 2-3-Tree, if you're lucky the height will stay the
   same. But you will not always be lucky. Sometimes the new element will make
   the tree just too big, and you will have the stuff to make a 2-node that is
   one level higher than the tree you started with. The following type
   expresses these possibilities. -}

  data Insertion23 (l u : BT)(n : Nat) : Set where
    itFits : T23 l u n -> Insertion23 l u n
    tooTall : (x : X) -> T23 l (# x) n -> T23 (# x) u n ->
              Insertion23 l u n

{- Implement insertion. You will need to use "with" for each recursive
   call, then inspect what happened and decide what to do. If the insertion
   fitted ok, you can just plug the new subtree back where it came from.
   If the result was "tooTall", you may be able to make something which
   fits by *rebalancing* the tree, which is the point of the thing. By keeping
   the tree balanced, we ensure a logarithmic access time for every element. -}

  insert23 : {l u : BT}{n : Nat} -> Interval l u -> T23 l u n -> Insertion23 l u n
  insert23 ilu tlu = {!!}

{- The following is a wrapper type for any old 2-3-Tree, of any height, with
   bot and top as bounds. It's as much as we can pin down about a tree that
   we build from the elements of an arbitrary list. -}

  record SomeT23 : Set where
    constructor [_]
    field
      {height} : Nat
      tree : T23 bot top height
  open SomeT23

  insertSomeT23 : X -> SomeT23 -> SomeT23
  insertSomeT23 x s = {!!}

  makeSomeT23 : List X -> SomeT23
  makeSomeT23 xs = {!!}

  flattenT23 : {l v u : BT}{n : Nat} ->
               T23 l v n ->
               OList l u
  flattenT23 t = {!!}

  sort23 : List X -> OList bot top
  sort23 xs = flattenT23 (tree (makeSomeT23 xs))

{- Here endeth the parametrized module -}

{- Now we can build one instance for the parameters -}

Le : Nat -> Nat -> Set
Le zero y = One
Le (suc x) zero = Zero
Le (suc x) (suc y) = Le x y

owoto : (x y : Nat) -> Le x y /+/ Le y x
owoto zero zero = inl <>
owoto zero (suc y) = inl <>
owoto (suc x) zero = inr <>
owoto (suc x) (suc y) = owoto x y

open OTreeSort owoto -- this gives us the Nat instance of all your sorting stuff

{- Here are some tests for your code! -}

myList : List Nat
myList =  20 :> 1 :> 18 :> 4 :> 13 :> 6 :> 10 :> 15 :> 2 :> 17 :>
          3 :> 19 :> 7 :> 16 :> 8 :> 11 :> 14 :> 9 :> 12 :> 5 :> []


myList' : OList bot top
myList' = 1 :> 2 :> 3 :> 4 :> 5 :> 6 :> 7 :> 8 :> 9 :> 10 :>
          11 :> 12 :> 13 :> 14 :> 15 :> 16 :> 17 :> 18 :> 19 :> 20 :> []

myTest1 : treeSort myList == myList'
myTest1 = refl

myTest2 : sort23 myList == myList'
myTest2 = refl
