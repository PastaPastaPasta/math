# ∃·BPTIME versus BPTS: the Mudigonda–Williams calculus stops at the golden ratio

For a Lean formalisation of the alternation-trading calculus of A. S. Mudigonda and R. R. Williams, "Time-Space Lower Bounds for Simulating Proof Systems with Quantum and Randomized Verifiers" (ITCS 2021, LIPIcs 185, article 50; full version arXiv 2012.00330), for ∃·BPTIME[n] versus randomized time n^c and space n^{o(1)} (BPTS):

- for every c ≥ 1, a refutation in the formalised rules exists if and only if c(c − 1) < 1, that is, if and only if c < φ = (1 + √5)/2 ≈ 1.618;
- the construction for c < φ uses only the exact rules of the paper's Definition 2.14 (rules 2–5, with Lemma 5.1 as the slowdown); a 15-step refutation at c = 1.467, above the paper's constant 1.4656 (the largest root of x³ − x² − 1), is checked separately;
- the impossibility for c ≥ φ holds in a relaxed calculus that also contains the unmerged orientation of the randomized speedup, speedups at the end points of their range, and weakening of exponents, and it excludes non-strict refutations as well;
- it also holds when lines need not alternate: adjacent blocks of the same type may be combined or split anywhere in the prefix at any later step (`MWL.StepX`, with the quantifier types of Theorem 2.10).

Both directions are kernel-checked in Lean. The construction repeats a move the source paper makes itself in the proof of its quantum result (its Theorem 5.4): the randomized speedup (Corollary 2.11) is applied again under the outer block (∃n⁰)¹ that the first randomized speedup leaves, so the cost of removing that block is paid once.

That the formal rules coincide with the paper's rules is a modelling claim, compared rule by rule on paper, not checked by Lean. The soundness of the paper's lemmas is not formalised; the published 1.4656 bound depends on them in the same way, in particular on its Lemma 5.2 (the hierarchy and contradiction step), which the paper only sketches. Conditional on the paper's Theorem 2.10, Corollaries 2.8 and 2.11, Lemma 5.1 and Lemma 5.2 (the last read with d′ < d, the direction its proof uses; the statement prints "d < d′" in both versions), the result gives ∃·BPTIME[n] ⊄ BPTS[n^c], and hence MATIME[n] ⊄ BPTS[n^c], for every c < φ. The proof of the paper's Theorem 5.3 uses the same results except Corollary 2.11, which it never applies; Corollary 2.11 is a stated result of the paper, used in the proof of its Theorem 5.4. Rules are compared against the definitions of the arXiv full version (in its Definition 2.4 both TS and BPTS machines have n^{o(1)} space, so TS ⊆ BPTS). This is a limit on one proof calculus, not a statement about lower bounds by other methods.

- Paper: [`paper/paper.tex`](paper/paper.tex) (reference version), the compiled [`paper/paper.pdf`](paper/paper.pdf), and [`paper/paper.md`](paper/paper.md). Rebuild the PDF with `tectonic paper.tex` or `pdflatex paper.tex` (run twice); regenerate `paper.md` with `python3 tex2md.py ../paper/paper.tex ../paper/paper.md` from [`scripts/`](scripts/) (needs pandoc).
- Lean code: [`../PastaMath/MWThreshold/`](../PastaMath/MWThreshold/)
- Exact-rational checker written from the paper's rules (the 15-step proof, the construction at c = 3/2 and 8/5, the c = 8/5 certificate, and the parameters of the paper's Theorem 5.3): [`scripts/`](scripts/)
- Reproducing the check: [`VERIFICATION.md`](VERIFICATION.md)
