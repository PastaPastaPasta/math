# Verifying the one-tape threshold result

## Build

Requirements: [elan](https://github.com/leanprover/elan) (it installs the Lean toolchain pinned in `lean-toolchain`, Lean 4.31.0) and `git`. From the repository root:

```sh
lake exe cache get   # download prebuilt Mathlib (pinned in lake-manifest.json)
lake build           # builds PastaMath, including PastaMath/OneTapeThreshold/Axioms.lean
```

The build must end with `Build completed successfully` and no errors or warnings. Recorded for this repository on an Apple M4 Pro laptop (14 cores), with Mathlib from the cache: a build of the whole `PastaMath` library from scratch ran 1891 jobs in about 4 min 40 s of wall time. Almost all of it is the three staircase certificates, which `decide +kernel` evaluates in the kernel:

| Module | Elaboration time |
|---|---|
| `PastaMath.OneTapeThreshold.StairD1` | 252 s (277 s in an earlier run) |
| `PastaMath.OneTapeThreshold.StairD2` | 50 s |
| `PastaMath.OneTapeThreshold.StairD3` | 28 s |
| `PastaMath.OneTapeThreshold.Ceiling` | 20 s |
| every other module | under 10 s |

The three certificate files are independent, so Lake builds them in parallel. `StairD1` takes longer on a slower machine; we have not timed it on the CI runner. The CI workflow sets no job timeout, so GitHub's default limit of 6 hours applies. Building only some modules, for example `lake build PastaMath.OneTapeThreshold.Dag`, checks no certificate; `lake build` (or `lake build PastaMath.OneTapeThreshold.Threshold`) is needed. To re-elaborate a single file without the cache, run `lake env lean PastaMath/OneTapeThreshold/StairD1.lean`.

While building `PastaMath.OneTapeThreshold.Axioms`, Lean prints one `#print axioms` line per headline theorem. To print them again on their own:

```sh
lake env lean PastaMath/OneTapeThreshold/Axioms.lean
```

## Expected axioms output

Every theorem must depend only on `propext`, `Classical.choice` and `Quot.sound` (the standard axioms of Lean's logic as used by Mathlib). `decide +kernel` adds no axiom. Output recorded for this repository (Lean 4.31.0, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`):

```
'PastaMath.OneTapeThreshold.conjecture_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.threshold_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD1_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD1_snf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD2_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD2_snf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD3_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD3_snf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.ceiling_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.ceiling_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.ceiling_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.cert39_above_r1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.no_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.nfCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HD.dagCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HDS.dagCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.sim' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.absCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.no_nf_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.no_nf_le_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.rstep_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The Lean files contain no `sorry`, `admit`, `native_decide`, `implemented_by` or `axiom` declarations, and no `import Mathlib.Tactic` umbrella import. The CI workflow (`.github/workflows/lean.yml`) checks this and the axioms output of every result on every push to `main`, on pull requests, and when run by hand (`workflow_dispatch`).

## Headline theorems

All names are in namespace `PastaMath.OneTapeThreshold`. The calculus is `HY.Step c d` (`Calculus.lean`), with one constructor per rule of Williams's §7 and his Lemma 3.3 inside a prefix: `convMerge`/`convNew` (Lemma 7.1, new block merged into the innermost block or opening a block of the other type), `speedMerge`/`speedNew` (Lemma 3.3, Speedup Rules 1 and 2) and `slow` (Lemma 7.2), with exact outputs and side conditions; the module docstring lists them. `HY.NF c d M n` is the strict normal form: `M 0, …, M n` (n ≥ 1) is a `Step` path from `([], T a)` to `([], T a')` with 1 ≤ a' < a, no line strictly between them has an empty block list, and every line alternates. `HL.RStep c d` (`Relaxed.lean`) is the relaxed calculus (outputs bounded only from below; quantifiers, guess exponents and the ≥ 1 floors dropped; input superscript 0 for the empty prefix), and `HL.sim` embeds `HY.Step` into it. `HDS.SpOK` says space ≤ time on a DTISP kernel.

| Theorem | File | Statement |
|---|---|---|
| `conjecture_fails` | `Threshold.lean` | For (d, c) = (1, 130921174/10⁸), (2, 11915968/10⁷), (3, 11386523/10⁷): there is `HY.NF c d M n` with `HY.pin (M i).1 ≤ (M i).2.time` and `HDS.SpOK (M i).2` for every i ≤ n, and every real root of `HY.pd d` (Williams's p_d) is below c. |
| `threshold_bounds` | `Threshold.lean` | For each d = 1, 2, 3: `HY.NF` proofs exist at c = 130921174/10⁸, 11915968/10⁷, 11386523/10⁷ respectively, and for every real c ≥ 6547/5000, 149/125, 712/625 respectively there is none. |
| `HStair.stairD1_nf`, `stairD2_nf`, `stairD3_nf` | `StairD1.lean`, … | ∃ M n, `HY.NF c d M n` at the three values above (via `HD.dagCheck_sound`). |
| `HStair.stairD1_snf`, `stairD2_snf`, `stairD3_snf` | `StairD1.lean`, … | The same, with kernel time ≥ input superscript and `HDS.SpOK` on every line (via `HDS.dagCheck_sound`). |
| `HLM.ceiling_d1`, `ceiling_d2`, `ceiling_d3` | `Ceiling.lean` | For every real c ≥ 6547/5000 (d = 1), 149/125 (d = 2), 712/625 (d = 3): (1) no `HY.NF c d M n`; (2) no `HL.RPath c d M n` with n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` with a' ≤ a₀; (3) every `HY.Step c d` path of length n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` has a₀ < a'. (2) and (3) put no condition on intermediate lines. |
| `HY.cert39_above_r1` | `Proof39.lean` | ∃ M n, `HY.NF (26019/20000) 1 M n`, and every real root of p₁ is below 26019/20000 = 1.30095. `HY.cert39_time`: every line of that 39-line proof has kernel time ≥ input superscript. |
| `HL.no_nf` | `Relaxed.lean` | For real d > 0, c ≥ 1 and c² ≥ 1 + 1/d there is no `HY.NF c d M n`. |
| `HY.nfCheck_sound` | `Calculus.lean` | Acceptance by the tag-list checker `HY.nfCheck c d a0 ts` gives ∃ M n, `HY.NF c d M n`. |
| `HD.dagCheck_sound`, `HDS.dagCheck_sound` | `Dag.lean`, `DagStrict.lean` | Acceptance by the DAG checker gives ∃ M n, `HY.NF c d M n`; for `HDS`, also kernel time ≥ input superscript and `HDS.SpOK` on every line. |
| `HL.sim` | `Relaxed.lean` | For c ≥ 0, every `HY.Step c d L L'` is an `HL.RStep c d (enc L) (enc L')`. |
| `HLM.absCheck_sound` | `AbsCheck.lean` | Acceptance by `HLM.absCheck c d θ₀ lv S` gives `HLM.Hyp` (the hypotheses of the multi-level potential, including the Lemma 7.1 condition for every word) for the data cast to ℝ. |
| `HLM.no_nf_of`, `HLM.no_nf_le_of` | `Potential.lean` | From `HLM.Hyp c₀ d θ₀ lv` and c₀ ≤ c: no `HY.NF c d M n`; and, if every θ (level 0 included) is > 1 and 1 < c₀, a₀ < a' along every `HY.Step c d` path of length ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')`. |
| `HLM.rstep_mono` | `Potential.lean` | For c₀ ≤ c, an `HL.RStep c d L L'` from a line with nonnegative entries is an `HL.RStep c₀ d L L'`. |

## What the build does not check

Lean checks statements about the *formal* calculus. It does not check:

- that `HY.Step` is Williams's calculus (a modelling claim, compared rule by rule in Table 2 and Section 2.4 of `paper/paper.tex`, with the calibration of Section 2.5);
- that `HL.RStep` covers every move of that calculus beyond `HL.sim` (paper Section 6, which also lists one sound move, DTIME_d[t] ⊆ DTISP[t, t] for d ≥ 2, that it does not cover);
- the soundness of Williams's lemmas (Lemmas 7.1, 7.2, 7.3, Lemma 3.3 inside a prefix, Theorem 3.1), on which the complexity reading SAT ∉ DTIME_d[n^c] for c below the lower values depends, as Williams's Theorem 7.5 does (paper Section 8);
- the staircase recursion and its threshold c*_stair, and the conjecture that the threshold of the calculus equals c*_stair (paper Section 7). The exact threshold is open.

The scripts in [`scripts/`](scripts/) re-check the certificates and the ceiling data in exact rationals, replay the 39-line proof and Williams's printed 25-line proof from Williams's text, and compute the numbers of paper Section 7; see [`scripts/README.md`](scripts/README.md). They are not part of the kernel-checked results.
