\chapter{Agda Mode Cheat Sheet}

I use standard emacs keystroke descriptions. E.g., `C-c' means control-c.
I delimit keystrokes with square brackets, but don't type the brackets or the
spaces between the individual key descriptions.


\section{Managing the buffer}

\subsection*{[C-c C-l] load buffer}

This keystroke tells Agda to resynchronize with the buffer contents, typechecking
everything. It will also make sure everything is displayed in the correct colour.


\section{Working in a goal}

The following apply only when the cursor is sitting inside the braces of a goal.

\subsection*{[C-c C-spc] give expression}

If you think you know which expression belongs in a goal, type the expression
between its braces, then use this keystroke. The expression can include |?|
symbols, which become subgoals.

\subsection*{[C-c C-c] case split}

If your goal is immediately to the right of |=|, then you're still building your
program's decision tree, so you can ask for a case analysis. Type the name of
a variable in the goal, then make this keystroke. Agda will try to split that
variable into its possible constructor patterns. Amusingly, if you type several
variables names and ask for a case analysis, you will get all the possible
combinations from splitting each of the variables.

\subsection*{[C-c C-a] ask Agsy (a.k.a. I feel lucky)}

If you make this keystroke, Agda will use a search mechanism called
`Agsy' to try and guess something with the right type.  Agsy may not
succeed. Even if it does, the guess may not be the right answer.
Sometimes, however, there's obviously only one sensible thing to do,
and then Agsy is your bezzy mate! It can be an incentive to make your
types precise!


\section{Checking and Testing things}

\subsection*{[C-c C-d] deduce type of expression}

If you type this keystroke, you will be prompted for an expression. If
the expression you supply makes sense, you will be told its type.

If you are working in a goal and have typed an expression already, Agda will
assume that you want the type of that expression.

\subsection*{[C-c C-n] normalize expression}

If you type this keystroke, you will be prompted for an expression. If
the expression you supply makes sense, you will be told its value.

If you are working in a goal and have typed an expression already, Agda will
assume that you want to normalize (i.e. compute as far as possible)
that expression. The normal form might not be a value, because there
might be some variables in your expression, getting in the way of
computation. When there are no free variables present, the normal form
is sure to be a value.