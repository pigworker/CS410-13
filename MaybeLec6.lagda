\section{An evaluator for well-typed (by construction) programs}

This time we shall revisit the well-typed evaluator, but instead of
using a predicate that ensures that the expression is well-typed we
shall index our expressions by their type -- making them well-typed
by construction.

\begin{code}
module MaybeLec6 where

open import BasicPrelude
open import Lec5 using (Expr; val; plus; le; ifThenElse; Type; NAT; TWO)

TyVal : Type -> Set
TyVal NAT = Nat
TyVal TWO = Two

data TyExpr : Type -> Set where
  val         : (T : Type) -> TyVal T -> TyExpr T
  plus        : TyExpr NAT -> TyExpr NAT -> TyExpr NAT
  le          : TyExpr NAT -> TyExpr NAT -> TyExpr TWO
  ifThenElse  : {T : Type} -> TyExpr TWO -> TyExpr T -> TyExpr T -> TyExpr T

evalType : Type -> Set
evalType NAT = Nat
evalType TWO = Two

eval : {T : Type} -> TyExpr T -> evalType T
eval (val NAT n)            = n
eval (val TWO b)            = b
eval (plus e1 e2)           = eval e1 + eval e2
eval (le e1 e2)             = eval e1 <= eval e2
eval (ifThenElse ec et ef)  = if eval ec then eval et else eval ef
\end{code}

Much nicer, is it not?

\paragraph{Exercise (not easy, but worth contemplating)} Why do we not
have to discharge ``bad'' cases manually or have to invert things like
last time?

\subsection{Some evaluator tests}

\begin{code}
testExpr1 : TyExpr NAT
testExpr1 = plus (val NAT 2) (val NAT 3)

testExpr2 : TyExpr TWO -> TyExpr NAT
testExpr2 b =  ifThenElse b
               testExpr1
               (val NAT 0)

test1 : eval testExpr1 == 5
test1 = refl

test2 : eval (testExpr2 (val TWO tt)) == 5
test2 = refl

test3 : eval (testExpr2 (le (val NAT 2) (val NAT 1))) == 0
test3 = refl
\end{code}

How do we parse a string (a source file of a program) into a well-typed
expression though?

\begin{verbatim}
  parse : String -> TyExpr ?
\end{verbatim}

How do we know the type? In this case we could infer it because our
language is so simple, but in general this is not possible (e.g. for
parts of Haskell and Agda).

Even if we could infer it, it is not a parser's job. A parser should
just parse concrete syntax (a string from a source file) into an
abstract syntax (a ``plain'' datatype), e.g.:

\begin{verbatim}
  parse : String -> Expr
\end{verbatim}

It is then the job of a typechecker to figure out if this is a
well-typed expression or not.

\begin{code}
data Maybe (A : Set) : Set where
  just : A -> Maybe A
  nothing : Maybe A

try : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
try nothing   k = nothing
try (just x)  k = k x

check : (e : Expr) (T : Type) -> Maybe (TyExpr T)
check (val (inl n))          NAT = just (val NAT n)
check (val (inl _))          TWO = nothing
check (val (inr _))          NAT = nothing
check (val (inr b))          TWO = just (val TWO b)
check (plus e1 e2)           NAT =  try (check e1 NAT)  \ wt1 ->
                                    try (check e2 NAT)  \ wt2 ->
                                    just (plus wt1 wt2)
check (plus e1 e2)           TWO = nothing
check (le e1 e2)             NAT = nothing
check (le e1 e2)             TWO =  try (check e1 NAT)  \ wt1 ->
                                    try (check e2 NAT)  \ wt2 ->
                                    just (le wt1 wt2)
check (ifThenElse ec et ef)  T =  try (check ec TWO)  \ wtc ->
                                  try (check et T)    \ wtt ->
                                  try (check ef T)    \ wtf ->
                                  just (ifThenElse wtc wtt wtf)
\end{code}

\subsection{Some typechecker tests}

Untyped expressions are sometimes called ``raw'', so let us use Agda's
module system to rename our previous examples accordingly:

\begin{code}
open import Lec5 using () renaming
  (testExpr1 to testRawExpr1; testExpr2 to testRawExpr2)
\end{code}

And then make sure that if we typecheck our raw expressions at the
appropriate type, we indeed get the well-typed expressions.

\begin{code}
testCheck1 : check testRawExpr1 NAT == just testExpr1
testCheck1 = refl

IsJust : {A : Set} -> Maybe A -> Set
IsJust nothing   = Zero
IsJust (just x)  = One

extract : {A : Set} -> (m : Maybe A) -> IsJust m -> A
extract nothing   p = magic p
extract (just x)  p = x

testCheck2 :  (b : Expr) (p : IsJust (check b TWO)) ->
              check (testRawExpr2 b) NAT ==
              just (testExpr2 (extract (check b TWO) p))
testCheck2 b p with check b TWO
testCheck2 b () | nothing
testCheck2 b p  | just _ = refl
\end{code}

\paragrahp{Exercise} Write more tests, make sure to include a couple
where typechecking nothings.

\paragraph{Exercise (hard)} The last test is more advanced then previous
ones, try figuring out what is going on.