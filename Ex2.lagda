% This is a literate Agda file -- it's both source code and
% documentation at the same time (you can generate a pdf from it using
% latex). Agda only checks stuff inside code blocks:
%
%  \begin{code}
%   ...
%  \end{code}
%
% Put your name in the \author field below for identification purposes!

\documentclass{article}
\usepackage[conor]{agda}

\title{Exercise 2 for CS410: \\ Extending Hutton's razor with effects}
\author{Put your name here}

\begin{document}
\maketitle

We have seen how Hutton's razor can be extended with booleans and
conditionals, next we shall investigate other extensions. In particular
we shall focus on effectful computations, the main goal of this exercise
is to notice a particular pattern that occurs every time we add an
effect.

\AgdaHide{
\begin{code}
module Ex2 where

open import BasicPrelude
\end{code}
}

% ----------------------------------------------------------------------
\section{The ability to fail}

\newcommand{\C}[1]{\AgdaInductiveConstructor{#1}}
\newcommand{\D}[1]{\AgdaDatatype{#1}}

This extension adds the ability to fail (an operation called
\C{fail}) and a way to recover from it (an operation called
\C{try\_default\_}).

The intended meaning of \C{fail} is that it allows the program to bail
out not giving a value (a natural number). We will model failure by
using the \D{Maybe} type (previously called \D{Dodgy}).

The intended meaning of \C{try\_default\_} is to try compute a value
from its first argument, if it succeeds doing so return that value
otherwise default to evaluating the second argument.

See and try to understand the tests below, before starting to fill in
the holes.

\begin{code}
-- We called this type Dodgy earlier.
data Maybe (A : Set) : Set where
  just     : A -> Maybe A
  nothing  : Maybe A

try : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
try (just x)  k = k x
try nothing   k = nothing
\end{code}

\begin{code}
module Fail where

  data Expr : Set where
    val           : Nat -> Expr
    plus          : Expr -> Expr -> Expr
    fail          : Expr
    try_default_  : Expr -> Expr -> Expr

  eval : Expr -> Maybe Nat
  eval (val x)            = just x
  eval (plus e1 e2)       = try (eval e1) \ v1 ->
                            try (eval e2) \ v2 ->
                            just (v1 + v2)
  eval fail               = {!!}
  eval (try e1 default e2)  = {!!}

  testExpr = plus (val 1) fail

  test : eval testExpr == nothing
  test = {!!}

  test2 : eval (plus (val 1) (try testExpr default val 2)) == just 3
  test2 = {!!}
\end{code}

% ----------------------------------------------------------------------
\section{The ability to throw an error}

This is a slight variation of the above extension, where we can supply
an error message in addition to bailing out (using the \C{throw}
operation).

Consequently error recovery becomes more interesting, as it can inspect
the error message (\C{try\_catch\_}) operation).

To model this kind of behaviour we will use the sum type (\D{Error}).

Again, see and understand the tests before continuing.

\begin{code}
module Error where

  data ErrorMsg : Set where
    someLameError   : ErrorMsg
    someOtherError  : ErrorMsg

  data Expr : Set where
    val         : Nat -> Expr
    plus        : Expr -> Expr -> Expr
    throw       : ErrorMsg -> Expr
    try_catch_  : Expr -> (ErrorMsg -> Expr) -> Expr

  Error : Set -> Set
  Error A = ErrorMsg /+/ A

  try' : {A B : Set} -> Error A -> (A -> Error B) -> Error B
  try' (inl err) k = {!!}
  try' (inr a)   k = {!!}

  eval : Expr -> Error Nat
  eval (val x)          = inr x
  eval (plus e1 e2)     = try' (eval e1) \ v1 ->
                          try' (eval e2) \ v2 ->
                          inr (v1 + v2)
  eval (throw err)      = {!!}
  eval (try e catch k)  = {!!}

  test : eval (try throw someLameError catch
           (\ { someLameError   -> val 1
              ; someOtherError  -> val 2
              })) == inr 1
  test = {!!}

  test2 : eval (try throw someOtherError catch
           (\ { someLameError   -> val 1
              ; someOtherError  -> val 2
              })) == inr 2
  test2 = {!!}

open Error using (Error)
\end{code}

% ----------------------------------------------------------------------
\section{The ability to store computations}

\newcommand{\F}[1]{\AgdaFunction{#1}}

This extension adds the ability to \C{store} and \C{load} the value of
an expression (not unlike the memory function on a calculator).

The intended meaning of \C{store} is to evaluate its argument, \F{put}
its value in the ``memory'' and then return it. \C{load} is supposed to
get the value from the memory.

We model this ``memory'' as a function from its current state to a value
and its new state (see \F{State}).

Again, see and understand the tests!

\begin{code}
module State where

  data Expr : Set where
    val    : Nat -> Expr
    plus   : Expr -> Expr -> Expr
    load   : Expr
    store  : Expr -> Expr

  State : Set -> Set -> Set
  State S A = S -> A /*/ S

  done : {A S : Set} -> A -> State S A
  done x = {!!}

  get : {S : Set} -> State S S
  get = \ s -> s , s

  put : {S : Set} -> S -> State S One
  put s = \ _ -> <> , s

  _bind_ : {S A B : Set} -> State S A -> (A -> State S B) -> State S B
  m bind k = {!!}

  eval : Expr -> State Nat Nat
  eval (val n)       = done n
  eval (plus e1 e2)  = eval e1 bind \ v1 ->
                       eval e2 bind \ v2 ->
                       done (v1 + v2)
  eval load          = {!!}
  eval (store e)     = {!!}

  test : eval (store (val 2)) 0 == 2 , 2
  test = {!!}

  test2 : eval (plus (store (val 2)) load) 0 == 4 , 2
  test2 = {!!}

  test3 : eval (plus load (store (val 2))) 0 == 2 , 2
  test3 = {!!}

  test4 : eval (plus load load) 3 == 6 , 3
  test4 = {!!}

open State using (State)
\end{code}

% ----------------------------------------------------------------------
\section{The ability to read from an environment}

Next we shall extend our language with \C{var}iables. The intended
meaning of variables is to return the value that they have been assigned
in some environment (see \F{Env}). We use \F{ask} to retrieve the
environment.

An expression is parametrised by a set which says how many variables it
has, in the tests we use expressions with two variables. The environment
is modelled as a function which assigns a value to each variable.

To model this we will use a variant of the ``memory''-cell above which
is read-only (see \F{Reader}).

\begin{code}
module Reader where

  data Expr (V : Set) : Set where
    val   : Nat -> Expr V
    plus  : Expr V -> Expr V -> Expr V
    var   : V -> Expr V

  -- Show how to substitue variables.
  subst : {V W : Set} -> Expr V -> (V -> Expr W) -> Expr W
  subst (val n)       r = {!!}
  subst (plus e1 e2)  r = {!!}
  subst (var x)       r = {!!}

  Reader : Set -> Set -> Set
  Reader R A = R -> A

  end : {A R : Set} -> A -> Reader R A
  end x = {!!}

  ask : {R : Set} -> Reader R R
  ask = \ r -> r

  _andThen_ : {R A B : Set} ->
              Reader R A -> (A -> Reader R B) -> Reader R B
  m andThen k = {!!}

  Env : Set -> Set
  Env V = V -> Nat

  eval : {V : Set} -> Expr V -> Reader (Env V) Nat
  eval (val n)                = end n
  eval (plus e1 e2)           = eval e1 andThen \ v1 ->
                                eval e2 andThen \ v2 ->
                                end (v1 + v2)
  eval (var x)                = {!!}

  test : eval (var tt) (\b -> if b then 1 else 2) == 1
  test = {!!}

  test2 : eval (var ff) (\b -> if b then 1 else 2) == 2
  test2 = {!!}

  test3 : eval (var <>) (\ _ -> 0) == 0
  test3 = {!!}

  test4 : eval {One} (subst (var <>) (\ _ -> val 3)) (\ _ -> 0) == 3
  test4 = {!!}

open Reader using (Reader)
\end{code}

% ----------------------------------------------------------------------
\section{The ability to do input and output}

This time we want to extend our language with the ability to \C{input}
and \C{output} values of expressions, we also want to be able to
sequence computations (the \C{>>} operator, pronounced ``then'').

The intended meaning is hopefully obvious. The way we model this
extensions is as a function from the input to a dodgy value and some
output. The reason for using a dodgy value is because it could be the
case that the program asks for input but the user doesn't provide any,
in which case we fail to provide a value (see \F{IO}).

Unlike previously, we do not evaluate straight from expressions into the
model, but instead we \F{build} up a strategy tree (see \D{IOTree})
\emph{representing} the computation and then \F{runIO} it to get the
intended meaning.

Going via a strategy tree is sometimes called doing a ``deep''-embedding
(as opposed to ``shallow''-embedding, which is what we been doing
earlier.) We shall discuss the advantages and disadvantages of both
approaches in class and touch on it in the exercises as well.

\begin{code}
module IO where

  infixl 1 _>>_

  data Expr : Set where
    val     : Nat -> Expr
    plus    : Expr -> Expr -> Expr
    input   : Expr
    output  : Expr -> Expr
    _>>_    : Expr -> Expr -> Expr

  data IOTree (A : Set) : Set where
    pure    : A -> IOTree A
    input   : One -> (Nat -> IOTree A) -> IOTree A
    output  : Nat -> (One -> IOTree A) -> IOTree A

  _graft_ : {A B : Set} -> IOTree A -> (A -> IOTree B) -> IOTree B
  pure x      graft k = {!!}
  input _ c   graft k = {!!}
  output n c  graft k = {!!}

  build : Expr -> IOTree Nat
  build (val n)       = pure n
  build (plus e1 e2)  = build e1 graft \ v1 ->
                        build e2 graft \ v2 ->
                        pure (v1 + v2)
  build input         = {!!}
  build (output e)    = {!!}
  build (e1 >> e2)    = {!!}

  Input  = List Nat
  Output = List Nat

  IO : Set -> Set
  IO A = Input -> Maybe A /*/ Output

  runIO : {A : Set} -> IOTree A -> IO A
  runIO (pure x)     is          = {!!}
  runIO (input _ k)   []         = {!!}
  runIO (input _ k)   (i :> is)  = {!!}
  runIO (output n k)  is         = {!!}

  eval : Expr -> IO Nat
  eval e = runIO (build e)

  test : eval (plus input input) (2 :> 3 :> []) == just 5 , []
  test = {!!}

  test2 :  eval (output (plus input input) >> val 1) (2 :> 3 :> []) ==
           just 1 , 5 :> []
  test2 = {!!}

  test3 :  eval (output (output (output (val 5)))) [] ==
           just 5 , 5 :> 5 :> 5 :> []
  test3 = {!!}

  test4 :  eval (output (val 1) >> output (val 2) >> input >> input)
                (0 :> 3 :> []) == just 3 , 1 :> 2 :> []
  test4 = {!!}

open IO using (IOTree)
\end{code}

% ----------------------------------------------------------------------
\section{The ability to log computations}

In the final extension we want to add the ability to log the value of
expressions using the \C{log\_>>\_} operator.

The intended meaning of this operator is to evaluate the first argument,
log its value and then return the value of its second argument.

Because this is the last extension we shall expect you to figure out how
to model this extension yourself (see \F{Writer}). \F{tell} should put
its argument in the log, and should come handy when giving the
\C{log\_>>\_} operator meaning.

\begin{code}
module Writer where

  data Expr : Set where
    val      : Nat -> Expr
    plus     : Expr -> Expr -> Expr
    log_>>_  : Expr -> Expr -> Expr

  Writer : Set -> Set -> Set
  Writer W A = {!!}

  finish : {A W : Set} -> A -> Writer W A
  finish x = {!!}

  tell : {W : Set} -> List W -> Writer W One
  tell ws = {!!}

  _combine_ : {W A B : Set} ->
              Writer W A -> (A -> Writer W B) -> Writer W B
  m combine k = {!!}

  eval : Expr -> Writer Nat Nat
  eval (val n)         = finish n
  eval (plus e1 e2)    = eval e1 combine \ v1 ->
                         eval e2 combine \ v2 ->
                         finish (v1 + v2)
  eval (log e1 >> e2)  = {!!}

  -- This should return 0 and the log should contain 1 and 2, finish the
  -- test once you implemented eval.
  test : eval (log val 1 >> log val 2 >> val 0) == {!!}
  test = {!!}

  -- This should return 5 and the log should contain 2 and 3.
  test2 : eval (plus (log val 2 >> val 2) (log val 3 >> val 3)) == {!!}
  test2 = {!!}

open Writer using (Writer)
\end{code}

% ----------------------------------------------------------------------
\section{Exercises}

Hopefully you have by now got some idea of how to model different
effects in object languages (extensions of Hutton's razor) using
constructs from the meta-language (Agda).

This process is called giving a denotational semantics, and it was
developed in the late 60s by Christopher Strachey and Dana Scott.


\paragraph{Exercise 1 (Moggi's insight)}

In the early 90s Eugenio Moggi, while working on giving denotational
semantics for effectful languages (just like we just have), noticed that
so called \emph{monads}\footnote{A construction from an abstract field
of mathematics called category theory.} could be used in every effectful
extension he cared about.

This is what a monad looks like:

\begin{code}
record Monad (M : Set -> Set) : Set1 where
  field
    return  : {A : Set} -> A -> M A
    _>>=_   : {A B : Set} -> M A -> (A -> M B) -> M B
\end{code}
%
And here is an instance of a monad:

\begin{code}
FailMonad : Monad Maybe
FailMonad = record { return = just; _>>=_ = try }
  where
  open Fail
\end{code}

\begin{enumerate}

  \item[(a)] Your task is to identify the rest of the monads.

\end{enumerate}

\begin{code}
ErrorMonad : Monad {!!}
ErrorMonad = record { return = {!!}; _>>=_ = {!!} }
  where
  open Error

StateMonad : {S : Set} -> Monad {!!}
StateMonad = record { return = {!!}; _>>=_ = {!!} }
  where
  open State

ReaderMonad : {R : Set} -> Monad {!!}
ReaderMonad = record { return = {!!}; _>>=_ = {!!} }
  where
  open Reader

ExprMonad : Monad Reader.Expr
ExprMonad = record { return = {!!}; _>>=_ = {!!} }
  where
  open Reader

IOTreeMonad : Monad {!!}
IOTreeMonad = record { return = pure; _>>=_ = _graft_ }
  where
  open IO

WriterMonad : {W : Set} -> Monad {!!}
WriterMonad = record { return = {!!}; _>>=_ = {!!} }
  where
  open Writer
\end{code}

\paragraph{Exercise 2 (The virtue of continuations)}

\begin{enumerate}

  \item[(a)] Rewrite the $\AgdaModule{State}$ module ``deep''-style.

\end{enumerate}

\begin{code}
module DeepState where

  data Expr : Set where
    val    : Nat -> Expr
    plus   : Expr -> Expr -> Expr
    load   : Expr
    store  : Expr -> Expr

  data Store (A : Set) : Set where
    return  : A -> Store A
    load    : One -> (Nat -> Store A) -> Store A
    store   : Nat -> (One -> Store A) -> Store A

  _graft_ : {A B : Set} ->
            Store A -> (A -> Store B) -> Store B
  return x   graft k = {!!}
  load _ c   graft k = load _ (\ n -> c n graft k)
  store n c  graft k = {!!}

  build : Expr -> Store Nat
  build (val n)       = {!!}
  build (plus e1 e2)  = {!!}
  build load          = {!!}
  build (store e)     = {!!}

  runState : {A : Set} -> Store A -> State Nat A
  runState (return x)   = {!!}
  runState (load _ k)   = {!!}
  runState (store n k)  = {!!}

  eval : Expr -> State Nat Nat
  eval e = runState (build e)

  test : eval (store (val 2)) 0 == 2 , 2
  test = {!!}

  test2 : eval (plus (store (val 2)) load) 0 == 4 , 2
  test2 = {!!}

  test3 : eval (plus load (store (val 2))) 0 == 2 , 2
  test3 = {!!}

  test4 : eval (plus load load) 3 == 6 , 3
  test4 = {!!}
\end{code}

\begin{enumerate}

  \item[(b)] Can you think of any reason why one would want to do it
   ``deep''-style rather than ``shallow''-style?

  \item[(c)] This exercise is not part of the homework, we will do it in
  class: Try rewriting the $\AgdaModule{IO}$ module ``shallow''-style.

  \item[(d)] This exercise is not part of the homework, we will do it in
   class: Can you figure out why it turns out to be trickier doing it
   that way?

\end{enumerate}

\paragraph{Exercise 3 (Wadler's insight)}

A couple of years after Moggi's insight, Philip Wadler realised that the
monads we use as denotations for different effectful extensions are also
interesting from a programming point of view in the meta-language.

For example here is a program that uses the \F{State} monad.

\begin{code}
prog : State Nat Two
prog =  get          >>= \ n ->
        put (suc n)  >>= \ _ ->
        return tt
  where
  open State
  open Monad StateMonad

test : prog 0 == tt , 1
test = {!!}
\end{code}

\begin{enumerate}

  \item[(a)] Write a stateful program which doubles the state and
  returns whether or not the result is less than 7. Write appropriate
  tests.

\end{enumerate}

\begin{code}
double>7 : State Nat Two
double>7 = {!!}
  where
  open State
  open Monad StateMonad
\end{code}

\begin{enumerate}

  \item[(b)] Write a program that uses \F{Writer} to reverse a list,
  together with appropriate tests.

\end{enumerate}

\begin{code}
logRev : List Nat -> Writer Nat One
logRev []         = {!!}
  where
  open Writer
  open Monad WriterMonad
logRev (x :> xs)  = {!!}
  where
  open Writer
  open Monad WriterMonad
\end{code}

\end{document}