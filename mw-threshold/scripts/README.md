# Scripts

`mw_check.py` is an exact checker for the calculus of A. S. Mudigonda and R. R. Williams for ∃·BPTIME[n] versus BPTS (arXiv 2012.00330, Definition 2.14 rules 2–5 with Lemma 5.1; numbering of the arXiv version), written from the paper's rules and independent of the Lean code. Python 3 standard library only; all arithmetic uses `fractions.Fraction`. Besides each rule's side condition 0 < x < d, it asserts that every line is orderly and alternates. The rules it implements are listed in the module docstring.

Run from this directory; each command takes well under a second.

```sh
python3 mw_check.py mw15                  # replay the 15-step refutation at c = 1.467 (paper §4.1)
python3 mw_check.py macro                 # one macro M(2) at c = 3/2: kernel factor exactly 27/28
python3 mw_check.py construct 3/2 8/5     # generate and check the construction of paper §4
python3 mw_check.py cert ../../PastaMath/MWThreshold/Cert.lean
                                          # regenerate the c = 8/5 certificate and compare it
                                          # with the tag list in the Lean file
python3 mw_check.py thm53                 # the parameters of the proof of Theorem 5.3 (paper §8)
python3 mw_check.py all ../../PastaMath/MWThreshold/Cert.lean
```

Expected results:

- `mw15`: final exponent 27410261545753261542320966055909/2750140100000000000000000000 ≈ 9966.86 < 10000.
- `construct`: at c = 3/2, macro M(2), ρ = 27/28, 12 macros, 61 steps, a₀ = 6.25 → 6.0595; at c = 8/5, macro M(5), ρ = 131072/131325 ≈ 0.99807, 244 macros, 2685 steps, a₀ ≈ 27.8954 → 27.8809.
- `cert`: the regenerated list (M(8), a₀ = 10000, T rounded up to six decimals, macro repeated while T ≥ 1; 158 macros, 2687 steps) is identical to the Lean certificate, and its replay ends at ≈ 110.93 < 10000.
- `thm53`: with the printed parameters x₁ = d/c³, x_i = (c(1 − ε))^{1−i} x₁, ε = 1/k, the condition c·x_i ≤ x_{i−1} fails for every k tried and d − Σx_i < 0 for k ≥ 5 (c = 1.40, 1.44, 1.46); with x_i = c^{k−i}T and d = σ_k T the best final/initial ratio over k ≤ 60 is 0.98054 at c = 1.46, 0.99799 at c = 1.465, 1.00151 at c = 1.466 and 1.01562 at c = 1.47.

These checks are evidence about the calculus as transcribed from the paper. They are not part of the kernel-checked results.

`tex2md.py` regenerates `../paper/paper.md` from `../paper/paper.tex` (the reference version): it resolves references, citations, theorem numbering and the bibliography, runs `pandoc -f latex -t gfm`, and adds the title block. It needs pandoc (tested with 3.12).

```sh
python3 tex2md.py ../paper/paper.tex ../paper/paper.md
```
