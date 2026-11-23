# Verifying the TAUT-threshold result

## Build

Requirements: [elan](https://github.com/leanprover/elan) (it installs the Lean toolchain pinned in `lean-toolchain`, Lean 4.31.0) and `git`. From the repository root:

```sh
lake exe cache get   # download prebuilt Mathlib (pinned in lake-manifest.json)
lake build           # builds PastaMath, including PastaMath/TautThreshold/Axioms.lean
```

The build must end with `Build completed successfully` and no errors. While building `PastaMath.TautThreshold.Axioms`, Lean prints one `#print axioms` line per headline theorem. To print them again on their own:

```sh
lake env lean PastaMath/TautThreshold/Axioms.lean
```

## Expected axioms output

Every theorem must depend only on `propext`, `Classical.choice` and `Quot.sound` (the standard axioms of Lean's logic as used by Mathlib). Output of the build recorded for this repository (Lean 4.31.0, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`):

```
'PastaMath.TautThreshold.TW.no_proofX' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.no_proofXE' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.no_nfX' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.normal_formX' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TL.no_trefutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TL.return_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.normal_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.normal_formE' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.no_literal_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.no_literal_proofE' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.no_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TD.dvmw' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TD.threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TDL.nf_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TDL.threshold_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.w5_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.wq_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.w13_combine' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TW.a27_combine' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TautThreshold.TL.tlv_refutes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The Lean files contain no `sorry`, `admit`, `native_decide`, `implemented_by` or `axiom` declarations; the CI workflow checks this and the axioms output on every push.

## Headline theorems

All names are in namespace `PastaMath.TautThreshold`. The rule relations are defined in `PastaMath/TautThreshold/Literal.lean`: `TW.WStepE` (exact rules of Williams's Lemmas 6.1 and 6.2, merging adjacent same-type blocks), `TW.WStep` (its relaxation: outputs only bounded below), `TW.WStepXE` (`WStepE` plus the exact non-merging speedup, matching-kernel flip and quantifier-free flip, and the identity (Q n^a)^a (Q n^b)^b = (Q n^{max(a,b)})^b of Williams's §2 applied in either direction to any two adjacent blocks) and `TW.WStepX` (the relaxation of `WStepXE`; lines need not alternate, and two adjacent same-type blocks anywhere in a line can be combined into one, or one block split into two). Lean proves `WStepE ⊆ WStep ⊆ WStepX` and `WStepXE ⊆ WStepX`. `TW.LineLE B A` means: same blocks and kernel type, and every exponent of B at most that of A.

| Theorem | File | Plain-language meaning |
|---|---|---|
| `TW.no_proofX` | `Literal.lean` | If c³ ≥ 4, no sequence of ≥ 1 extended (relaxed) rule steps takes any line A to a line B with `LineLE B (compl A)`; in particular not to ¬A. |
| `TW.no_proofXE` | `Literal.lean` | The same for the exact extended rules. |
| `TW.no_literal_proof`, `TW.no_literal_proofE` | `Literal.lean` | Corollaries: no path from A to ¬A in the relaxed or exact merging rules. |
| `TW.no_nfX` | `Literal.lean` | If c³ ≥ 4, there is no normal-form proof NTS[n^a] ⊆ … ⊆ coNTS[n^{a'}] with a' ≤ a (Williams's Definition 6.4) in the extended rules. |
| `TW.no_nf` | `Literal.lean` | Corollary: the same for the relaxed merging rules `WStep` (hence for `WStepE`). |
| `TW.normal_form`, `TW.normal_formE`, `TW.normal_formX` | `Literal.lean` | For every c, a proof of A ⊆ ¬A yields a normal-form proof in the same rule set (analogue of Williams's Theorem 6.6). |
| `TL.no_trefutation` | `Limit.lean` | If c³ ≥ 4, the reduced homogeneous calculus `TL.TStep` has no normal-form refutation. |
| `TL.return_bound` | `Limit.lean` | If c³ ≥ 4, a reduced path of ≥ 2 steps from depth 0 (exponent a₀ ≥ 0) that stays at positive depth and returns to depth 0 ends with exponent ≥ (min(c,2)²/2)·a₀ ≥ 2^{1/3}·a₀. |
| `TD.dvmw`, `TD.threshold` | `DvMW.lean` | For c ≥ 1, the reduced calculus has a refutation iff c³ < 4. |
| `TDL.nf_exists` | `DvMWLiteral.lean` | For 1 ≤ c with c³ < 4, a normal-form proof exists using only the exact merging rules (the Diehl–van Melkebeek–Williams construction). |
| `TDL.threshold_literal` | `DvMWLiteral.lean` | For c ≥ 1: a normal-form proof with the exact merging rules exists iff c³ < 4. |
| `TW.w5_nf`, `TW.wq_proof`, `TL.tlv_refutes` | `Literal.lean`, `Limit.lean` | Non-vacuity: concrete proofs at c = 5/4 and c = 13/10 are accepted by the definitions. |
| `TW.w13_combine`, `TW.a27_combine` | `Literal.lean` | Non-vacuity: the §2 identity (∃n)¹(∃n)¹ NTS[n] ⊆ (∃n)¹ NTS[n] is one `WStepXE` step, and the combining step on p. A:27 of Williams's paper is one `WStepX` step. |

## What the build does not check

Lean checks the theorems about the formal calculus. It does not check that the formal rules cover the rules of Williams's paper (a modelling claim; the remaining reading points, such as dropping n^{o(1)} terms from the exponents, are listed in Section 9(b) of `paper/paper.tex`), or that the calculus is sound for complexity classes. Williams's Lemma 6.5 (a normal-form proof contradicts the hypothesis) is cited only for proofs in the published calculus: in `WStepX`, `flipQ` alone gives a two-line normal-form proof at c = 1, which Lemma 6.5's argument does not cover. The existence direction uses only `WStepE`.

The scripts in [`scripts/`](scripts/) (Python standard library, exact rational arithmetic) check numbers quoted from Williams's paper; they are not part of the kernel-checked results. Run them with `python3 scripts/w13_listing.py` (well under a second) and `python3 scripts/w13_lp.py --lines 5,8,11` (about a minute) from this directory; `python3 scripts/w13_lp.py --lines 14 --digits 3` takes several minutes.
