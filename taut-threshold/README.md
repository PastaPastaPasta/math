# TAUTOLOGY versus NTS: the alternation-trading calculus stops at ∛4

For a Lean formalisation of the alternation-trading proof calculus of R. Williams, "Alternation-Trading Proofs, Linear Programming, and Lower Bounds" (ACM TOCT 2013), Section 6 (TAUTOLOGY versus nondeterministic time n^c and space n^{o(1)}):

- for c³ ≥ 4, no sequence of rule applications takes a line A to its complement ¬A, or to any line componentwise below ¬A, and no normal-form proof exists (Williams's Conjecture 6.8, for the formalised calculus, including c = ∛4);
- for c ≥ 1, a normal-form proof exists if and only if c³ < 4.

Both directions are kernel-checked in Lean. The impossibility theorem is proved for an extended rule set (`TW.WStepX`) that contains the exact rules of Williams's Lemmas 6.1 and 6.2 with merging of adjacent same-type blocks, and also the variants a literal reading of the printed lemmas allows: speedups that open a block next to one of the same type without merging (so lines need not alternate), in-place flips of a matching kernel, and flips of a quantifier-free kernel. The existence direction uses only the exact merging rules.

That these rules cover the published calculus is a modelling claim checked on paper, not by Lean. The reading points that remain are: n^{o(1)} terms are dropped from the exponents (s = 0 in Lemma 6.1, following Williams's convention that such factors do not affect exponents), the input constraint in front of the outermost block is 1, and the speedup for a coNTS kernel is the complement of the NTS rule. Soundness of the calculus is published, not formalised. This is a limit on one proof calculus, not a statement about TAUTOLOGY lower bounds by other methods.

- Paper: [`paper/paper.tex`](paper/paper.tex) (reference version), the compiled [`paper/paper.pdf`](paper/paper.pdf), and [`paper/paper.md`](paper/paper.md). Rebuild the PDF with `tectonic paper.tex` or `pdflatex paper.tex` (run twice).
- Lean code: [`../PastaMath/TautThreshold/`](../PastaMath/TautThreshold/)
- Scripts checking the numbers cited from Williams's paper (Section 9(d) of the paper): [`scripts/`](scripts/)
- Reproducing the check: [`VERIFICATION.md`](VERIFICATION.md)
