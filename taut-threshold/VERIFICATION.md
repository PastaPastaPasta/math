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
'PastaMath.TautThreshold.TL.no_trefutation' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'PastaMath.TautThreshold.TL.tlv_refutes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The Lean files contain no `sorry`, `admit`, `native_decide`, `implemented_by` or `axiom` declarations; the CI workflow checks this and the axioms output on every push.

## Headline theorems

All names are in namespace `PastaMath.TautThreshold`. "Formal calculus" means `TW.WStep` (relaxed rules) or `TW.WStepE` (exact rules of Williams's Lemmas 6.1 and 6.2), defined in `PastaMath/TautThreshold/Literal.lean`.

| Theorem | File | Plain-language meaning |
|---|---|---|
| `TW.no_literal_proof` | `Literal.lean` | If c³ ≥ 4, no sequence of ≥ 1 relaxed rule steps takes any line A to its complement ¬A. |
| `TW.no_literal_proofE` | `Literal.lean` | The same for the exact rules. |
| `TW.no_nf` | `Literal.lean` | If c³ ≥ 4, there is no normal-form proof NTS[n^a] ⊆ … ⊆ coNTS[n^{a'}] with a' ≤ a (Williams's Definition 6.4). |
| `TW.normal_form`, `TW.normal_formE` | `Literal.lean` | For every c, a proof of A ⊆ ¬A yields a normal-form proof in the same rule set (analogue of Williams's Theorem 6.6). |
| `TL.no_trefutation` | `Limit.lean` | If c³ ≥ 4, the reduced homogeneous calculus `TL.TStep` has no normal-form refutation. |
| `TD.dvmw`, `TD.threshold` | `DvMW.lean` | For c ≥ 1, the reduced calculus has a refutation iff c³ < 4. |
| `TDL.nf_exists` | `DvMWLiteral.lean` | For 1 ≤ c with c³ < 4, a normal-form proof exists using only the exact rules (the Diehl–van Melkebeek–Williams construction). |
| `TDL.threshold_literal` | `DvMWLiteral.lean` | For c ≥ 1: a normal-form proof with the exact rules exists iff c³ < 4. |
| `TW.w5_nf`, `TW.wq_proof`, `TL.tlv_refutes` | `Literal.lean`, `Limit.lean` | Non-vacuity: concrete proofs at c = 5/4 and c = 13/10 are accepted by the definitions. |

## What the build does not check

Lean checks the theorems about the formal calculus. It does not check that the formal rules are the rules of Williams's paper, or that the calculus is sound for complexity classes. See Section 8 of `paper/paper.tex` for the full list.
