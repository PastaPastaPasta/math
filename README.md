# math

Mathematical results by PastaPastaPasta, each with a written proof and, where available, a Lean 4 formalisation checked against Mathlib.

## Results

| Directory | Result | Lean |
|---|---|---|
| [`taut-threshold/`](taut-threshold/) | The alternation-trading calculus of Williams (TOCT 2013, §6) for TAUTOLOGY versus NTS, as formalised, has threshold exactly ∛4: for c³ ≥ 4 there is no proof of A ⊆ ¬A (nor of A ⊆ B for any B componentwise below ¬A) and no normal-form proof, and for 1 ≤ c < ∛4 normal-form proofs exist. The formal rules include merged and non-merged same-type blocks, combining and splitting of adjacent same-type blocks anywhere in a line, and matching-kernel and quantifier-free flips; the remaining modelling choices (e.g. n^{o(1)} terms dropped) are listed in the paper. | [`PastaMath/TautThreshold/`](PastaMath/TautThreshold/) |

Each result directory has its own README, the paper (LaTeX source, compiled PDF and a Markdown rendering), and a `VERIFICATION.md` saying what is machine-checked and how to reproduce it.

## Building the Lean code

The repository is one Lake package, library `PastaMath`, pinned to Lean 4.31.0 and a fixed Mathlib revision (`lean-toolchain`, `lake-manifest.json`). With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

CI (`.github/workflows/lean.yml`) runs the same build on every push and checks the axioms of the headline theorems.

## AI assistance

The proofs and formalisations in this repository were produced with Anthropic's Claude models under the author's direction. For each result, the kernel-checked Lean proofs are the primary evidence; the papers state what is and is not machine-checked.

## Licence

- Code (`PastaMath/`, `PastaMath.lean`, `*/scripts/*.py`, the Lake configuration and CI files): Apache License 2.0, see [`LICENSE-APACHE`](LICENSE-APACHE).
- Papers and other text (`*/paper/`, README and Markdown files): Creative Commons Attribution 4.0 International (CC BY 4.0), see [`LICENSE-CC-BY-4.0`](LICENSE-CC-BY-4.0).

Both licences permit reuse with attribution. Copyright PastaPastaPasta.
