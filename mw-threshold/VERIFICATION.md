# Verifying the MW-threshold result

## Build

Requirements: [elan](https://github.com/leanprover/elan) (it installs the Lean toolchain pinned in `lean-toolchain`, Lean 4.31.0) and `git`. From the repository root:

```sh
lake exe cache get   # download prebuilt Mathlib (pinned in lake-manifest.json)
lake build           # builds PastaMath, including PastaMath/MWThreshold/Axioms.lean
```

The build must end with `Build completed successfully` and no errors or warnings. With Mathlib from the cache, a build of the whole `PastaMath` library from scratch took about 19 s of wall time on an Apple-silicon laptop; the c = 8/5 certificate (`PastaMath/MWThreshold/Cert.lean`, checked with `decide +kernel`) took 7.5 s of it. While building `PastaMath.MWThreshold.Axioms`, Lean prints one `#print axioms` line per headline theorem. To print them again on their own:

```sh
lake env lean PastaMath/MWThreshold/Axioms.lean
```

## Expected axioms output

Every theorem must depend only on `propext`, `Classical.choice` and `Quot.sound` (the standard axioms of Lean's logic as used by Mathlib). `decide +kernel` adds no axiom. Output recorded for this repository (Lean 4.31.0, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`):

```
'PastaMath.MWThreshold.MWG.threshold_phi' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWG.threshold_goldenRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWG.refutes_of_lt_phi' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWL.no_lit_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MW.no_mrefutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MW.qf_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWG.threshold_phi_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWL.no_litU_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MW.no_urefutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWG.threshold_phi_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWL.no_litW_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MW.no_wrefutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MW.qf_ge_w' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MW.phi_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWG.threshold_phi_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWL.no_litX_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MW.no_xrefutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MW.qf_ge_x' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWL.lit_x' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWL.lit_m' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWL.checkQ_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWG.mw15_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWG.mw15_refutes' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWG.mw21_root_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWL.mwcert_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.MWThreshold.MWL.mw_refutes_8_5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The Lean files contain no `sorry`, `admit`, `native_decide`, `implemented_by` or `axiom` declarations, and no `import Mathlib.Tactic` umbrella import; the CI workflow checks this and the axioms output of both results on every push to `main` and on pull requests.

## Headline theorems

All names are in namespace `PastaMath.MWThreshold`. The calculus is defined in `Literal.lean`: `MWL.Step c` has one constructor per rule of the source paper (arXiv numbering): `rspeed0` (rule 3, Theorem 2.10), `rspeed` (rule 4, Corollary 2.11, merged as its footnote prescribes), `dspeed` (rule 2, Corollary 2.8) and `slow` (rule 5, Lemma 5.1), with the exact output values and the side conditions 0 < x < a. `MWL.Refutes c n M` says that `M 0, …, M n` (n ≥ 1) is a `Step` path from BPTS[n^{a₀}], a₀ > 0, to a quantifier-free BPTS[n^{a'}] with a' < a₀. `MWL.StepU` adds the unmerged orientation of rule 4 (Theorem 2.10 under a block without absorbing its leading n⁰ block), and `MWL.StepW` adds weakening (raise any exponent of an existing line, keeping the number of blocks, the quantifiers and each guess exponent at most its output, or replace a TS kernel by BPTS). `MWL.StepX` (LP form, quantifiers kept) lets lines stop alternating: it adds Lemma 2.7 with Q = Q_k before merging, the unmerged rule 4 with a leading block of either type, and `combine`/`split` of adjacent same-type blocks anywhere in the prefix at any step; every `Step` and `StepW` step is a `StepX` step (`MWL.step_stepX`, `MWL.stepW_stepX`). The relaxed calculus `MW.MStep` (`Limit.lean`) drops quantifiers and guess exponents, bounds every output and the new kernel exponent only from below, allows 0 ≤ x ≤ a, rule 3 on either kernel and rule 4 on TS kernels, and uses input exponent 0; `MW.UStep` and `MW.StepW` add the unmerged randomized speedup and weakening. `MW.XStep` adds `rspeedS` and `slowIn`, the two rules the run encoding `MWL.encR` (one entry per maximal run of same-type blocks) needs; under that encoding combining and splitting are weakenings.

| Theorem | File | Plain-language meaning |
|---|---|---|
| `MWG.threshold_phi` | `Threshold.lean` | For every real c ≥ 1: a strict refutation (`MWL.Refutes`, from a₀ > 0) in the exact rules exists iff c(c − 1) < 1. |
| `MWG.threshold_goldenRatio` | `Threshold.lean` | The same with the condition written as c < (1 + √5)/2 (Mathlib's `Real.goldenRatio`). |
| `MWG.refutes_of_lt_phi` | `Threshold.lean` | Construction: if 1 ≤ c and c(c − 1) < 1, a strict refutation exists in the exact rules (a macro iterated under the outer (∃n⁰)¹ block, then one final slowdown). |
| `MWL.no_lit_refutation` | `Literal.lean` | If c > 0 and c² ≥ c + 1 (that is, c ≥ φ), there is no refutation in the exact rules (`Refutes` is strict; non-strict refutations are excluded by `no_litU_refutation`, since `Step ⊆ StepU`). |
| `MW.no_mrefutation`, `MW.qf_ge` | `Limit.lean` | The same in the relaxed calculus, also for non-strict refutations (a' ≤ a₀, from a₀ > 0, ≥ 1 step); `qf_ge`: for a₀ ≥ 0, every quantifier-free line BPTS[n^{a'}] reached from BPTS[n^{a₀}] in ≥ 1 step has a' ≥ c·a₀. |
| `MWG.threshold_phi_U`, `MWL.no_litU_refutation`, `MW.no_urefutation` | `Threshold.lean`, `Literal.lean`, `Limit.lean` | The threshold (for c ≥ 1) and the limit (for c > 0, c² ≥ c + 1) are unchanged when the unmerged orientation of the randomized speedup is added; these exclude non-strict refutations (a' ≤ a₀, from a₀ > 0, ≥ 1 step). |
| `MWG.threshold_phi_W`, `MWL.no_litW_refutation`, `MW.no_wrefutation`, `MW.qf_ge_w` | `Threshold.lean`, `Literal.lean`, `Limit.lean` | The same when weakening is added as well: no non-strict refutation from a₀ > 0 with at least one rule step; `qf_ge_w`: for a₀ ≥ 0, if an `MW.StepW` path from BPTS[n^{a₀}] with at least one rule step ends at a quantifier-free line BPTS[n^{a'}], then a' ≥ c·a₀. |
| `MW.phi_mono` | `Limit.lean` | For any g satisfying `MW.Facts c g` (the proof uses g = 1/(c² − 1), which satisfies it when c > 0 and c² ≥ c + 1), the potential Φ of the limit proof does not decrease under a weakening (raising exponents, TS → BPTS) of a line with nonnegative entries. |
| `MWG.threshold_phi_X`, `MWL.no_litX_refutation`, `MW.no_xrefutation`, `MW.qf_ge_x` | `Threshold.lean`, `Literal.lean`, `Limit.lean` | The threshold (for c ≥ 1) and the limit (for c > 0, c² ≥ c + 1) are unchanged when lines need not alternate and same-type blocks may be combined or split at any step: no non-strict refutation from a₀ > 0 that passes through a line with a quantifier block; `qf_ge_x`: for a₀ ≥ 0, if an `MW.XStep` path from BPTS[n^{a₀}] that passes through a line with a block ends at a quantifier-free line BPTS[n^{a'}], then a' ≥ c·a₀. |
| `MWL.lit_x` | `Literal.lean` | For c ≥ 0: every `StepX` step from a line with nonnegative output and kernel exponents is an `MW.XStep` step of the run encodings, and the resulting line again has nonnegative output and kernel exponents (a `StepX` step can introduce a negative guess exponent). |
| `MWL.lit_m` | `Literal.lean` | For c ≥ 0: every step of the exact rules from an orderly line with nonnegative exponents is a step of the relaxed calculus between the encodings (output and kernel exponents), and the resulting line again satisfies that invariant. |
| `MWL.checkQ_sound` | `Literal.lean` | A tag list accepted by the executable rational checker `MWL.checkQ` (a₀ > 0, nonempty list, legal replay ending at BPTS[n^{a'}] with a' < a₀) gives a strict refutation at the same c. |
| `MWG.mw15_ok`, `MWG.mw15_refutes` | `Threshold.lean` | A 15-step refutation at c = 1467/1000 from a₀ = 10⁴ (checked with `decide +kernel`): the rule sequence of two M(3) macros with chosen parameters, then the final slowdown. |
| `MWG.mw21_root_lt` | `Threshold.lean` | Every real root of x³ − x² − 1 (the source paper's Theorem 5.3) is below 1467/1000. |
| `MWL.mwcert_ok`, `MWL.mw_refutes_8_5` | `Cert.lean` | A 2687-step refutation at c = 8/5 (checked with `decide +kernel`; redundant given `refutes_of_lt_phi`). |

## What the build does not check

Lean checks the threshold of the *formal* calculus in both directions. It does not check that the formal rules coincide with the rules of the source paper (a modelling claim, compared rule by rule in Table 1 and the reading points of `paper/paper.tex`, Section 2), or that the paper's lemmas are sound: Theorem 2.10 (quoted from Diehl and van Melkebeek, with a proof sketch), Corollaries 2.8 and 2.11, Lemma 5.1, and Lemma 5.2 (read with d′ < d), the hierarchy and contradiction step, which the paper only sketches. The published 1.4656 bound depends on these lemmas in the same way, except that its proof does not use Corollary 2.11. The complexity-theoretic consequence (∃·BPTIME[n] ⊄ BPTS[n^c] for c < φ) is therefore conditional on them; Section 7 of the paper gives the argument. Outside the formalisation are contradictions other than BPTS[n^d] ⊆ … ⊆ BPTS[n^{d'}], the reading of rule 4 with arbitrary quantifier types together with combining, and rules acting at other positions than the formal ones: speedups and slowdowns act at the kernel end (the innermost block), combining and splitting may act anywhere in the prefix, and weakening acts componentwise on the whole line (paper Section 6).

The script [`scripts/mw_check.py`](scripts/mw_check.py) (Python standard library, exact rational arithmetic) is an independent transcription of the paper's rules. It replays the 15-step proof, checks the contraction factor 27/28 at c = 3/2, generates and checks the construction at c = 3/2 and 8/5, regenerates the Lean c = 8/5 certificate and compares it, and checks the parameters printed in the proof of the paper's Theorem 5.3. It is not part of the kernel-checked results. Run it with `python3 scripts/mw_check.py all ../PastaMath/MWThreshold/Cert.lean` from this directory (well under a second).
