# math

Mathematical results by PastaPastaPasta, each with a written proof and, where available, a Lean 4 formalisation checked against Mathlib.

## Results

| Directory | Result | Lean |
|---|---|---|
| [`taut-threshold/`](taut-threshold/) | The alternation-trading calculus of Williams (TOCT 2013, §6) for TAUTOLOGY versus NTS has threshold exactly ∛4: no proof for c³ ≥ 4, normal-form proofs for all 1 ≤ c < ∛4. | [`PastaMath/TautThreshold/`](PastaMath/TautThreshold/) |

Each result directory has its own README, the paper (LaTeX and Markdown), and a `VERIFICATION.md` saying what is machine-checked and how to reproduce it.

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

- Lean code (`PastaMath/`, `PastaMath.lean`, the Lake configuration and CI files): Apache License 2.0, see [`LICENSE-APACHE`](LICENSE-APACHE).
- Papers and other text (`*/paper/`, README and Markdown files): Creative Commons Attribution 4.0 International (CC BY 4.0), see [`LICENSE-CC-BY-4.0`](LICENSE-CC-BY-4.0).

Both licences permit reuse with attribution. Copyright PastaPastaPasta.
