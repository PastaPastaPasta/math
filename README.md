# math

Mathematical results by PastaPastaPasta, each with a written proof and, where available, a Lean 4 formalisation checked against Mathlib.

## Results

| Directory | Result | Lean |
|---|---|---|
| [`taut-threshold/`](taut-threshold/) | The alternation-trading calculus of Williams (TOCT 2013, §6) for TAUTOLOGY versus NTS, as formalised, has threshold exactly ∛4: for c³ ≥ 4 there is no proof of A ⊆ ¬A (nor of A ⊆ B for any B componentwise below ¬A) and no normal-form proof, and for 1 ≤ c < ∛4 normal-form proofs exist. The formal rules include merged and non-merged same-type blocks, combining and splitting of adjacent same-type blocks anywhere in a line, and matching-kernel and quantifier-free flips; the remaining modelling choices (e.g. n^{o(1)} terms dropped) are listed in the paper. | [`PastaMath/TautThreshold/`](PastaMath/TautThreshold/) |
| [`mw-threshold/`](mw-threshold/) | The alternation-trading calculus of Mudigonda and Williams (ITCS 2021) for ∃·BPTIME[n] versus BPTS (randomized time n^c, space n^{o(1)}), as formalised, has threshold exactly the golden ratio φ: for c ≥ 1 a refutation exists if and only if c(c − 1) < 1. The construction (for 1 ≤ c < φ) uses only the exact rules and includes a 15-step refutation at c = 1.467, above the paper's 1.4656; the impossibility also covers the unmerged randomized speedup, weakening, and combining same-type blocks at any later step. That the formal rules match the paper's is a modelling claim checked on paper, and the lower bound ∃·BPTIME[n] ⊄ BPTS[n^c] for c < φ is conditional on the paper's Theorem 2.10, Corollaries 2.8 and 2.11, Lemma 5.1 and its sketched Lemma 5.2 (read with d′ < d, the direction its proof uses; the statement prints "d < d′"); its 1.4656 bound rests on the same results except Corollary 2.11. | [`PastaMath/MWThreshold/`](PastaMath/MWThreshold/) |
| [`onetape-threshold/`](onetape-threshold/) | The alternation-trading calculus of Williams (TOCT 2013, §7) for SAT on machines with one d-dimensional sequential work tape, as formalised, has normal-form proofs at c = 1.30921174, 1.1915968, 1.1386523 for d = 1, 2, 3, above the exponents r_d of Williams's Theorem 7.5, so his conjecture that r_d is optimal fails for the formalised calculus; and for c ≥ 1.3094, 1.192, 1.1392 respectively it has none from any starting exponent a₀ > 0, strict or non-strict, even in a relaxed calculus whose step outputs are bounded only from below (it also contains Speedup Rule 2 and unmerged creation of blocks), and also with the inclusion DTIME_d[t] ⊆ DTISP[t, t] added. These ceilings are theorems about the formalised rule set (the formal rules plus the extensions named in each theorem), which is our reading of Williams's lemmas as set out in Section 2.4 of the paper; his proof sketches display some lines that differ from it, and for some of those (for example the smaller output superscripts of the log n block displayed in his sketch of Theorem 7.9) the ceilings are not established. The scope table in Section 2.4 is the full statement; its list is not claimed exhaustive. Every displayed derivation step of Williams's §7 is compared with the formal rules in an appendix of the paper. The threshold thus lies in [1.30921174, 1.3094], [1.1915968, 1.192], [1.1386523, 1.1392]; its exact value is open, and that it equals the numerically estimated staircase value ≈ 1.30921174467760 (d = 1) is a conjecture supported by numerics only. That the formal rules match Williams's is a modelling claim checked on paper; the lower bound SAT ∉ DTIME_d[n^c] below the three values is conditional on Williams's Lemmas 7.1, 7.2, 7.3, his Lemma 3.3 inside a prefix, the combining of same-type blocks (his §2) and his Theorem 3.1 with Corollary 3.2, as his Theorem 7.5 is. | [`PastaMath/OneTapeThreshold/`](PastaMath/OneTapeThreshold/) |

Each result directory has its own README, the paper (LaTeX source, compiled PDF and a Markdown rendering), and a `VERIFICATION.md` saying what is machine-checked and how to reproduce it.

## Building the Lean code

The repository is one Lake package, library `PastaMath`, pinned to Lean 4.31.0 and a fixed Mathlib revision (`lean-toolchain`, `lake-manifest.json`). With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

CI (`.github/workflows/lean.yml`) runs the same build on every push to `main`, on pull requests and when run by hand, and checks the axioms of the headline theorems. The one-tape certificates make the build take several minutes (see `onetape-threshold/VERIFICATION.md`).

## AI assistance

The proofs and formalisations in this repository were produced with Anthropic's Claude models under the author's direction. For each result, the kernel-checked Lean proofs are the primary evidence; the papers state what is and is not machine-checked.

## Licence

- Code (`PastaMath/`, `PastaMath.lean`, `*/scripts/*.py`, the Lake configuration and CI files): Apache License 2.0, see [`LICENSE-APACHE`](LICENSE-APACHE).
- Papers and other text (`*/paper/`, README and Markdown files): Creative Commons Attribution 4.0 International (CC BY 4.0), see [`LICENSE-CC-BY-4.0`](LICENSE-CC-BY-4.0).

Both licences permit reuse with attribution. Copyright PastaPastaPasta.
