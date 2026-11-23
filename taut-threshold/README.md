# TAUTOLOGY versus NTS: the alternation-trading calculus stops at ∛4

For a Lean formalisation of the alternation-trading proof calculus of R. Williams, "Alternation-Trading Proofs, Linear Programming, and Lower Bounds" (ACM TOCT 2013), Section 6 (TAUTOLOGY versus nondeterministic time n^c and space n^{o(1)}):

- for c³ ≥ 4, no sequence of rule applications takes a line to its complement, and no normal-form proof exists (Williams's Conjecture 6.8, for the formalised calculus, including c = ∛4);
- for c ≥ 1, a normal-form proof exists if and only if c³ < 4.

Both directions are kernel-checked in Lean. That the formal rules coincide with the published calculus is a modelling claim checked on paper, and soundness of the calculus is published, not formalised. This is a limit on one proof calculus, not a statement about TAUTOLOGY lower bounds by other methods.

- Paper: [`paper/paper.tex`](paper/paper.tex) (reference version) and [`paper/paper.md`](paper/paper.md). No PDF is checked in; build one with `pdflatex paper.tex` (run twice).
- Lean code: [`../PastaMath/TautThreshold/`](../PastaMath/TautThreshold/)
- Reproducing the check: [`VERIFICATION.md`](VERIFICATION.md)
