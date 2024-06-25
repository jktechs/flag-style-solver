This binairy has one argument: The string to parse and prove.
If left empty it will instead listen for a line on stdin.

This is the format for the propositions:
characters | meaning
--- | ---
=> | Implication
<=> | Biconditional
/\\ | Conjunction
\\/ | Disjunction
! | Inversion
T | True
F | False
any capital letter | Variable

Presidence goes in this order:
1. Inversion
1. Conjunction and Disjunction
1. Implication
1. Biconditional