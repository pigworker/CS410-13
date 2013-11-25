module Lec10 where

open import BasicPrelude

record Functor (F : Set{-type of elements-} -> Set{-type of structures-})
  : Set1 where
  field

    map : {S T : Set} -> (S -> T)    {- operation on elements-} 
                      -> F S -> F T  {- operation on structures -}

    mapI : {X : Set}(xs : F X) -> map id xs == xs
    mapC : {R S T : Set}(f : S -> T)(g : R -> S)(xs : F R) ->
              map f (map g xs) == map (f o g) xs

open Functor public

ListFunctor : Functor List
ListFunctor = record { map = mapList; mapI = mapIList; mapC = mapCList } where

  mapList : {S T : Set} -> (S -> T) -> List S -> List T
  mapList f [] = []
  mapList f (x :> xs) = f x :> mapList f xs

  mapIList : {X : Set} (xs : List X) -> mapList id xs == xs
  mapIList [] = refl
  mapIList (x :> xs) rewrite mapIList xs = refl

  mapCList : {R S T : Set} (f : S -> T) (g : R -> S) (xs : List R) ->
               mapList f (mapList g xs) == mapList (f o g) xs
  mapCList f g [] = refl
  mapCList f g (x :> xs) rewrite mapCList f g xs = refl

Label : Set -> (Set -> Set)  -- no elements
Label A X = A

LabelFunctor : (A : Set) -> Functor (Label A)
LabelFunctor A = record
  { map = \ _ a -> a; mapI = \ _ -> refl; mapC = \ _ _ _ -> refl }

Id : Set -> Set  -- one element
Id X = X

IdFunctor : Functor Id
IdFunctor = record {
              map = id;
              mapI = \ _ -> refl;
              mapC = \ _ _ _ -> refl }

PairFunctor : {F G : Set -> Set} -> Functor F -> Functor G ->
              Functor \ X -> F X /*/ G X
PairFunctor {F}{G} FunF FunG = record { map = mapP ; mapI = mapPI ; mapC = mapPC }
  where
  mapP : {S T : Set} -> (S -> T) -> (F S /*/ G S) -> (F T /*/ G T)
  mapP f (xF , xG) = map FunF f xF , map FunG f xG
  mapPI : forall {X : Set}(xs : F X /*/ G X) -> mapP id xs == xs
  mapPI (xF , xG) rewrite mapI FunF xF | mapI FunG xG = refl
  mapPC : {R S T : Set} (f : S -> T) (g : R -> S) (xs : F R /*/ G R) ->
          mapP f (mapP g xs) == mapP (f o g) xs
  mapPC f g (xF , xG) rewrite mapC FunF f g xF | mapC FunG f g xG = refl

SumFunctor : {F G : Set -> Set} -> Functor F -> Functor G ->
              Functor \ X -> F X /+/ G X
SumFunctor {F}{G} FunF FunG = record { map = mapS ; mapI = mapSI; mapC = mapSC }
  where
  mapS : {S T : Set} -> (S -> T) -> (F S /+/ G S) -> (F T /+/ G T)
  mapS f (inl xF) = inl (map FunF f xF)
  mapS f (inr xG) = inr (map FunG f xG)
  mapSI : {X : Set} (xs : F X /+/ G X) -> mapS id xs == xs
  mapSI (inl xF) rewrite mapI FunF xF = refl
  mapSI (inr xG) rewrite mapI FunG xG = refl
  mapSC : {R S T : Set} (f : S -> T) (g : R -> S) (xs : F R /+/ G R) ->
           mapS f (mapS g xs) == mapS (f o g) xs
  mapSC f g (inl xF) rewrite mapC FunF f g xF = refl
  mapSC f g (inr xG) rewrite mapC FunG f g xG = refl

data Kit : Set1 where
  labelK : Set -> Kit
  idK : Kit
  _*K_ : Kit -> Kit -> Kit
  _+K_ : Kit -> Kit -> Kit

infixr 4 _+K_
infixr 5 _*K_

Fun : Kit -> Set -> Set
Fun (labelK A) X = Label A X
Fun idK X = Id X
Fun (f *K g) X = Fun f X /*/ Fun g X
Fun (f +K g) X = Fun f X /+/ Fun g X

FunFunctor : (f : Kit) -> Functor (Fun f)
FunFunctor (labelK A) = LabelFunctor A
FunFunctor idK = IdFunctor
FunFunctor (f *K g) = PairFunctor (FunFunctor f) (FunFunctor g)
FunFunctor (f +K g) = SumFunctor (FunFunctor f) (FunFunctor g)

data DATA (f : Kit) : Set where
  [_] : Fun f (DATA f) -> DATA f

mysteryf : Kit
mysteryf = (labelK One) +K idK

MYSTERY : Set
MYSTERY = DATA mysteryf

{- -- ask Agsy to try making some elements of the MYSTERY type
mystery : MYSTERY
mystery = {!-l!}  -- do [C-c C-a] with -l in the braces
-}

-- Aha! It's a copy of the natural numbers!

zeroM : MYSTERY
zeroM = [ inl <> ]

sucM : MYSTERY -> MYSTERY
sucM n = [ inr n ]

-- Now how about this...

treef : Set -> Kit
treef X = labelK One   +K   idK *K labelK X *K idK

pattern leaf = [ inl <> ]
pattern node l x r = [ inr (l , x , r) ]

flatten : {X : Set} -> DATA (treef X) -> List X
flatten leaf          = []
flatten (node l x r)  = flatten l ++ x :> flatten r

insert : Nat -> DATA (treef Nat) -> DATA (treef Nat)
insert n leaf = node leaf n leaf
insert n (node l x r) with n <= x 
insert n (node l x r) | tt = node (insert n l) x r
insert n (node l x r) | ff = node l x (insert n r)

StuffINeed : Kit -> Set
StuffINeed (labelK A) = A -> A -> Two
StuffINeed idK = One
StuffINeed (f *K g) = StuffINeed f /*/ StuffINeed g
StuffINeed (f +K g) = StuffINeed f /*/ StuffINeed g

kitEq : {f : Kit} -> StuffINeed f -> DATA f -> DATA f -> Two

nodeEq : (r : Kit) -> StuffINeed r -> (f : Kit) -> StuffINeed f ->
          Fun f (DATA r) -> Fun f (DATA r) -> Two
nodeEq r sr (labelK A) s a a' = s a a'
nodeEq r sr idK s x y = kitEq sr x y
nodeEq r sr (f *K g) (sf , sg) (xf , xg) (yf , yg)
   with nodeEq r sr f sf xf yf | nodeEq r sr g sg xg yg
nodeEq r sr (f *K g) (sf , sg) (xf , xg) (yf , yg) | tt | tt  = tt
nodeEq r sr (f *K g) (sf , sg) (xf , xg) (yf , yg) | qf | qg  = ff
nodeEq r sr (f +K g) s (inl xf) (inl yf) = nodeEq r sr f (outl s) xf yf
nodeEq r sr (f +K g) s (inl xf) (inr yg) = ff
nodeEq r sr (f +K g) s (inr xg) (inl yf) = ff
nodeEq r sr (f +K g) s (inr xg) (inr yg) = nodeEq r sr g (outr s) xg yg

kitEq {f} s [ x ] [ y ] = nodeEq f s f s x y

myGo : Two
myGo = kitEq ((\ _ _ -> tt) , _) (sucM (sucM (sucM zeroM))) (sucM (sucM (sucM zeroM)))