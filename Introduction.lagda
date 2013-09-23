\chapter{Introduction}


\section{Language and Tools}

For the most part, we'll be using the experimental language,
Agda~\cite{DBLP:conf/afp/Norell08}, which is a bit like Haskell
(and implemented in Haskell), but has a more expressive type system
and a rather fabulous environment for typed programming. Much of what
we learn here can be ported back to Haskell with a bit of bodging and
fudging (and perhaps some stylish twists), but it's the programming
environment that makes it worth exploring the ideas in this class via
Agda.

The bad news, for some of you at any rate, is that the Agda programming
environment is tightly coupled to the Emacs editor. If you don't like
Emacs, tough luck. You may have a job getting all this stuff to work on
whatever machines you use outside the department, but the toolchain all
works fine on departmental machines.

Teaching materials, exercise files, lecture scripts, and so on, will
all pile up in the repository
\url{https://github.com/pigworker/CS410-13}, so you'll need to get
with the git programme. We'll fix it so you each have your own place
to put your official branch of the repo where I can get at it. All
work and feedback will be mediated via your git repository.


\section{Lectures, Lab, Tutorials}

\textbf{Monday:~} Lecture and Lab, 2--5pm LT1301

\textbf{Tuesday:~} Tutorial, 4--5pm, GH718 (this will usually be
  conducted by one of my graduate students)

\textbf{Friday:~} Lecture, 11am--12pm, GH811

\textbf{Scheduled interruptions of service:~} Monday 30 September,
University closed; Week 4 (14--18 October), I'm at a working group
meeting; perhaps Friday 8 November, when I might be examining a PhD.
We can't do anything about the University closing, but I'll try to
find fun people for you to hang out with on the other dates.


\section{Twitter @@CS410afp}

This class has a twitter feed. Largely, this is so that I can post
pictures of the whiteboard. I don't use it for essential
communications about class business, so you need neither join twitter
nor follow this user. You can access all the relevant stuff just by
surfing into \url{http://twitter.com/CS410afp}. This user, unlike my
personal account, will follow back all class members who follow it,
unless you ask it not to.


\section{Hoop Jumping}

CS410 Advanced Functional Programming is a level 4 class worth 20
credits.  It is assessed \emph{entirely} by coursework. Departmental
policy requires class convenors to avoid deadline collisions by
polite negotiation, so I've agreed the following dates for handins,
as visible on the 4th year noticeboard.
\begin{itemize}
\item Thursday week 3
\item Friday week 6
\item Thursday week 9
\item Tuesday week 12
\item Wednesday week 15
\item final assignment, issued as soon as possible after fourth year project
  deadline, to be submitted as late as I consider practicable
  before the exam board
\end{itemize}
In order to ensure sufficient evidence of independent learning,
I reserve the right to conduct done-in-one-lab assignments on Mondays
not in a deadline week, and to conduct oral examinations by
appointment.



\section{Getting Agda Going on Departmental Machines}

Step 1. Use Linux. Get yourself a shell. (It's going to be that sort
of a deal, all the way along. Welcome back to the 1970s.)

Step 2. Ensure that your \texttt{PATH} environment variable includes
the directory where Haskell's \texttt{cabal} build manager puts
executables. Under normal circumstances, this is readily achieved by
ensuring that your \texttt{.profile} file contains the line:
\[
\mbox{\texttt{export PATH=\$HOME/.cabal/bin:\$PATH}}
\]
After you've edited \texttt{.profile}, grab a fresh shell window before
continuing.

Step 3. Ensure that you are in sync with the Haskell package database
by issuing the command:
\[
\mbox{\texttt{cabal update}}
\]

Step 4. Install Agda by issuing the command:
\[
\mbox{\texttt{cabal install agda}}
\]
Yes, that's a lower case 'a' in 'agda'.

Step 5. Wait.

Step 6. Wait some more.

Step 7. Assuming all of that worked just fine, set up the Emacs interactive environment with the command:
\[
\mbox{\texttt{agda-mode setup; agda-mode compile}}
\]

Step 8. Get this repository. Navigate to where in your file system you want
to keep it and do
\[
\mbox{\texttt{git clone https://github.com/pigworker/CS410-13.git}}
\]

Step 9. Navigate into the repo.
\[
\mbox{\texttt{cd CS410-13}}
\]

Step 10. Start an emacs session involving an Agda file, e.g., by the command:
\[
\mbox{\texttt{emacs Hello.agda \&}}
\]


\section{Making These Notes}

The sources for these notes are included in the repo along with
everything else. They're built using the excellent \texttt{lhs2TeX}
tool, developed by Andres L\"oh and Ralf Hinze. This, also, can be
summoned via the Haskell package manager.
\[
\mbox{\texttt{cabal install lhs2tex}}
\]
With that done, the default action of \texttt{make} is to build
these notes as \texttt{CS410.pdf}.


\section{What's in \texttt{Hello.agda}?}

It starts with a \texttt{module} declaration, which should and does
match the filename.

\begin{verbatim}
module Hello where
\end{verbatim}

Then, as in Haskell, we have comments-to-end-of-line, as signalled by
\texttt{ --~} with a space.

\begin{verbatim}
-- Oh, you made it! Well done! This line is a comment.

-- In the beginning, Agda knows nothing, but we can teach it about numbers.
\end{verbatim}

Indeed, this module has not \texttt{import}ed any others, and unlike in
Haskell, there is no implicit `Prelude', so at this stage, the only thing
we have is the notion of a \texttt{Set}. The following \texttt{data}
declaration creates three new things---a new \texttt{Set}, populated
with just the values generated by its constructors.

\begin{verbatim}
data Nat : Set where
  zero  :  Nat
  suc   :  Nat -> Nat
\end{verbatim}

We see some key differences with Haskell. Firstly, \emph{one} colon
means `has type', rather than `list cons'. Secondly, rather than
writing `templates' for data, we just state directly the types of the
constructors. Thirdly, there's a lot of space: Agda has very simple
rules for splitting text into tokens, so space is often necessary,
e.g., around \texttt{:} or \texttt{ ->}. It is my habit to use even
more space than is necessary for disambiguation, because I like to
keep things in alignment.

Speaking of alignment, we do have the similarity with Haskell that
indentation after \texttt{where} indicates subordination, showing that
the declarations of the \texttt{zero} and \texttt{suc} value
constructors belong to the declaration of the \texttt{Nat} type
constructor.

Another difference is that I have chosen to begin the names of
\texttt{zero} and \texttt{suc} in \emph{lower} case. Agda enforces no
typographical convention to distinguish constructors from other things,
so we can choose whatever names we like. It is conventional in Agda to
name data-like things in lower case and type-like things in upper case.
Crucially, \texttt{zero}, \texttt{suc}, \texttt{Nat} and \texttt{Set}
all live in the \emph{same} namespace. The distinction between different
kinds of things is achieved by referring back to their declaration, which
is the basis for the colour scheme in the emacs interface.

The declaration of \texttt{Nat} tells us exactly which values the new set
has. When we declare a function, we create new \emph{expressions} in a
type, but \emph{no new values}. Rather, we explain which value should
be returned for every possible combination of inputs.

\begin{verbatim}
-- Now we can say how to add numbers.

_+_ : Nat -> Nat -> Nat
zero   +  n  = n
suc m  +  n  = suc (m + n)
\end{verbatim}

What's in a name? When a name includes \emph{underscores}, they stand
for places you can put arguments in an application. The unspaced
\texttt{\_+\_} is the name of the function, and can be used as an
ordinary identifier in prefix notation, e.g. \texttt{\_+\_ m n} for
\texttt{m + n}.  When we use \texttt{+} as an infix operator (with
arguments in the places suggested by the underscores), the spaces
around it are necessary. If we wrote \texttt{m+n} by accident, we would
find that it is treated as a whole other symbol.

Meanwhile, because there are no values in \texttt{Nat} other than
those built by \texttt{zero} and \texttt{suc}, we can be sure that
the definition of \texttt{+} covers all the possibilities for the
inputs. Moreover, or rather, lessunder, the recursive call in the
\texttt{suc} case has as its first argument a smaller number than
in the pattern on the left hand side, so the recursive call is
strictly simpler. Assuming (rightly, in Agda), that \emph{values}
are not recursive structures, we must eventually reach \texttt{zero},
so that every addition of values is bound to yield a value.

\begin{verbatim}
-- Now we can try adding some numbers.

four : Nat
four = (suc (suc zero)) + (suc (suc zero))

-- To make it go, select "Evaluate term to normal form" from the
-- Agda menu, then type "four", without the quotes, and press return.

-- Hopefully, you should get a response
--   suc (suc (suc (suc zero)))
\end{verbatim}

Evaluation shows us that although we have enriched our expression
language with things like $2+2$, the values in \texttt{Nat} are exactly
what we said they were: there are no new numbers, no error cases, no
`undefined's, no recursive black holes, just the values we declared.

That is to say, Agda is a language of \emph{total} programs. You can
approach it on the basis that things mean what they say, and---unusually
for programming languages---you will usually be right.