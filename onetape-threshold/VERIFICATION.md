# Verifying the one-tape threshold result

## Build

Requirements: [elan](https://github.com/leanprover/elan) (it installs the Lean toolchain pinned in `lean-toolchain`, Lean 4.31.0) and `git`. From the repository root:

```sh
lake exe cache get   # download prebuilt Mathlib (pinned in lake-manifest.json)
lake build           # builds PastaMath, including PastaMath/OneTapeThreshold/Axioms.lean
```

The build must end with `Build completed successfully` and no errors or warnings. Recorded for this repository on an Apple M4 Pro laptop (14 cores), with Mathlib from the cache: a build of the whole `PastaMath` library from scratch ran 1891 jobs in about 4 min 40 s of wall time (before `Variants.lean` and `Displays.lean` were added; the library now has 1893 jobs), and a rebuild of the one-tape modules after a change to `Calculus.lean` took 2 min 42 s. In short: about 2–5 minutes on an idle machine, longer under load; on a loaded or slower machine the build can take several times longer. Almost all of it is the three staircase certificates, which `decide +kernel` evaluates in the kernel:

| Module | Elaboration time |
|---|---|
| `PastaMath.OneTapeThreshold.StairD1` | 138–277 s on an idle machine (141 s in the latest run); up to 959 s has been measured on a loaded machine |
| `PastaMath.OneTapeThreshold.StairD2` | 40–50 s |
| `PastaMath.OneTapeThreshold.StairD3` | 22–28 s |
| `PastaMath.OneTapeThreshold.Ceiling` | 16–20 s |
| every other module | under 10 s |

The three certificate files are independent, so Lake builds them in parallel. `StairD1` takes longer on a slower or loaded machine (up to 959 s measured); we have not timed it on the CI runner. The CI workflow sets no job timeout, so GitHub's default limit of 6 hours applies. Building only some modules, for example `lake build PastaMath.OneTapeThreshold.Dag`, checks no certificate; `lake build` (or `lake build PastaMath.OneTapeThreshold.Threshold`) is needed. To re-elaborate a single file without the cache, run `lake env lean PastaMath/OneTapeThreshold/StairD1.lean`.

While building `PastaMath.OneTapeThreshold.Axioms`, Lean prints one `#print axioms` line per headline theorem (49 lines). To print them again on their own:

```sh
lake env lean PastaMath/OneTapeThreshold/Axioms.lean
```

## Expected axioms output

Every theorem must depend only on `propext`, `Classical.choice` and `Quot.sound` (the standard axioms of Lean's logic as used by Mathlib). `decide +kernel` adds no axiom. Output recorded for this repository (Lean 4.31.0, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`):

```
'PastaMath.OneTapeThreshold.conjecture_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.threshold_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.conjecture_fails_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.conjecture_fails_O' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.conjecture_fails_in' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.conjecture_fails_sp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD1_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD1_snf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD2_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD2_snf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD3_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD3_snf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD1_snfO' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD2_snfO' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HStair.stairD3_snfO' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.ceiling_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.ceiling_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.ceiling_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.cert39_above_r1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.cert39_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.no_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.ceilingX_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.ceilingX_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.ceilingX_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.no_drop_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.path_unwiden' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.nfCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HD.dagCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HDS.dagCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HD.dagCheck_soundO' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HDS.dagCheck_soundO' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.sim' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.absCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.no_nf_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.no_nf_le_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HLM.rstep_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.slow_convMerge_A34' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.slow_convMerge_A34O' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.path_S_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.path_S_space_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.path_S_space_nonnegO' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.cor78_base_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.path_alt' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HY.path_alt_incl' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.rstep_T_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.threshold_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.no_nfO' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.rpathW_last_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.OneTapeThreshold.HL.qf_ge_W' depends on axioms: [propext, Classical.choice, Quot.sound]

```

The Lean files contain no `sorry`, `admit`, `native_decide`, `implemented_by` or `axiom` declarations, and no `import Mathlib.Tactic` umbrella import. The CI workflow (`.github/workflows/lean.yml`) checks this and the axioms output of every result on every push to `main`, on pull requests, and when run by hand (`workflow_dispatch`).

## Headline theorems

All names are in namespace `PastaMath.OneTapeThreshold`. The calculus is `HY.Step c d` (`Calculus.lean`), with one constructor per rule of Williams's §7 and his Lemma 3.3 inside a prefix: `convMerge`/`convNew` (Lemma 7.1, new block merged into the innermost block or opening a block of the other type), `speedMerge`/`speedNew` (Lemma 3.3, Speedup Rules 1 and 2) and `slow` (Lemma 7.2), with exact outputs and side conditions; the module docstring lists them. `HY.NF c d M n` is the strict normal form: `M 0, …, M n` (n ≥ 1) is a `Step` path from `([], T a)` to `([], T a')` with 1 ≤ a' < a, no line strictly between them has an empty block list, and every line alternates. `HL.RStep c d` (`Relaxed.lean`) is the relaxed calculus (outputs bounded only from below; quantifiers, guess exponents and the ≥ 1 floors dropped; input superscript 0 for the empty prefix), and `HL.sim` embeds `HY.Step` into it. `HDS.SpOK` says space ≤ time on a DTISP kernel. Two moves outside `HY.Step` are defined in `Variants.lean`: `HY.Incl`, the inclusion DTIME_d[n^a] ⊆ DTISP[n^a, n^a] under any prefix (from `(bl, T a)` to `(bl, S a a)`), with relaxed form `HL.Widen` (to `(bl, S a₂ e₂)` with a ≤ a₂, a ≤ e₂); and `HY.SpeedLog`, Lemma 3.3 in a prefix with the side conditions of `speedMerge`/`speedNew` but any output superscript ℓ ≥ 0 for the new log n block, with relaxed form `HL.Loose`. `HL.RPathX c d M n` is a path of `RStep c d` and `Widen` steps. `HY.StepO ℓ c d` (`Calculus.lean`) is `HY.Step` with the output superscript of the new log n block of Lemma 3.3 given by a function ℓ of the input superscript and the space exponent (`StepO max` is `Step`), and `HY.NFO ℓ` its strict normal form; `HY.LogOK ℓ` says 1 ≤ ℓ(o, e) ≤ max(o, e) for o ≥ 1, e ≥ 0 (`HY.logOK_max`, `HY.logOK_one`, `HY.logOK_in` for max(o, 1), `HY.logOK_sp` for max(1, e)). `HY.StepO (fun _ _ => 1)` is the calculus in which that block has output exactly 1. Every `StepO ℓ` step keeps Lemma 3.3's guess exponent max(g, x + e) and the full maximum of Lemma 7.2.

| Theorem | File | Statement |
|---|---|---|
| `conjecture_fails` | `Threshold.lean` | For (d, c) = (1, 130921174/10⁸), (2, 11915968/10⁷), (3, 11386523/10⁷): there is `HY.NF c d M n` with `HY.pin (M i).1 ≤ (M i).2.time` and `HDS.SpOK (M i).2` for every i ≤ n, and every real root of `HY.pd d` (Williams's p_d) is below c. |
| `conjecture_fails_one` | `Threshold.lean` | The existence part of `conjecture_fails` with `HY.NFO (fun _ _ => 1)` in place of `HY.NF`: strict normal-form proofs, with kernel time ≥ input superscript and `HDS.SpOK` on every line, in the calculus in which the new log n block of Lemma 3.3 has output exactly 1 (from `HStair.stairD{1,2,3}_snf1`, via `HDS.dagCheck_sound1`). |
| `conjecture_fails_O` | `Threshold.lean` | For every ℓ with `HY.LogOK ℓ`: the existence part of `conjecture_fails` with `HY.NFO ℓ` in place of `HY.NF` (from `HStair.stairD{1,2,3}_snfO`, via `HDS.dagCheck_soundO`). |
| `conjecture_fails_in`, `conjecture_fails_sp` | `Threshold.lean` | `conjecture_fails_O` for ℓ(o, e) = max(o, 1) (the output displayed in Case 1 of Williams's sketch of Theorem 7.9, p. A:37) and for ℓ(o, e) = max(1, e) (the output Lemma 3.3 states for a quantifier-free class). |
| `threshold_bounds` | `Threshold.lean` | For each d = 1, 2, 3: `HY.NF` proofs exist at c = 130921174/10⁸, 11915968/10⁷, 11386523/10⁷ respectively, and for every real c ≥ 6547/5000, 149/125, 712/625 respectively there is none. |
| `threshold_sup` | `Threshold.lean` | With `cstar d = sSup {c : ℝ ∣ ∃ M n, HY.NF c d M n}` and `cstarX d` the same for `HY.NFX` (the strict normal form whose steps are `HY.Step c d` or `HY.Incl` steps, `Variants.lean`): 130921174/10⁸ ≤ `cstar 1` ≤ 6547/5000, 11915968/10⁷ ≤ `cstar 2` ≤ 149/125, 11386523/10⁷ ≤ `cstar 3` ≤ 712/625, and the same for `cstarX`. (Mathlib's `sSup` on ℝ is the supremum for nonempty sets bounded above; the proof obtains both from `threshold_bounds` and `HLM.ceilingX_d{1,2,3}`.) |
| `HStair.stairD1_nf`, `stairD2_nf`, `stairD3_nf` | `StairD1.lean`, … | ∃ M n, `HY.NF c d M n` at the three values above (via `HD.dagCheck_sound`). |
| `HStair.stairD1_snf`, `stairD2_snf`, `stairD3_snf` | `StairD1.lean`, … | The same, with kernel time ≥ input superscript and `HDS.SpOK` on every line (via `HDS.dagCheck_sound`). |
| `HStair.stairD1_snfO`, `stairD2_snfO`, `stairD3_snfO` | `StairD1.lean`, … | For every ℓ with `HY.LogOK ℓ`: the same with `HY.NFO ℓ` (via `HDS.dagCheck_soundO`). |
| `HLM.ceiling_d1`, `ceiling_d2`, `ceiling_d3` | `Ceiling.lean` | For every real c ≥ 6547/5000 (d = 1), 149/125 (d = 2), 712/625 (d = 3): (1) no `HY.NF c d M n`; (2) no `HL.RPath c d M n` with n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` with a' ≤ a₀; (3) every `HY.Step c d` path of length n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` has a₀ < a'. (2) and (3) put no condition on intermediate lines. |
| `HY.cert39_above_r1` | `Proof39.lean` | ∃ M n, `HY.NF (26019/20000) 1 M n`, and every real root of p₁ is below 26019/20000 = 1.30095. (`HY.cert39_time` is the Boolean check that every line of the rational replay of `cert39` from `([], T 100000)` has `pinQ` ≤ kernel time.) |
| `HY.cert39_spec` | `Proof39.lean` | ∃ M, `HY.NF (26019/20000) 1 M 38` (39 lines, each step a `HY.Step`) with `M 0 = ([], T 100000)` and `HY.pin (M i).1 ≤ (M i).2.time` for every i ≤ 38; and every real root of p₁ is below 26019/20000. |
| `HL.no_nf` | `Relaxed.lean` | For real d > 0, c ≥ 1 and c² ≥ 1 + 1/d there is no `HY.NF c d M n`. |
| `HLM.ceilingX_d1`, `ceilingX_d2`, `ceilingX_d3` | `Variants.lean` | For every real c ≥ 6547/5000 (d = 1), 149/125 (d = 2), 712/625 (d = 3): (1) no `HL.RPathX c d M n` with n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` with a' ≤ a₀; (2) every path of `HY.Step c d` and `HY.Incl` steps of length n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` has a₀ < a'. |
| `HL.no_drop_W` | `Variants.lean` | For real d ≥ 1, c ≥ 1 and c² ≥ 1 + 1/d: along every path of `HY.Step c d`, `HY.Incl` and `HY.SpeedLog` steps from `([], T a₀)`, a₀ ≥ 0, to `([], T a')`, a₀ ≤ a'. (This excludes strict normal forms, a' < a₀, not a path with a' = a₀.) |
| `HL.no_nfO` | `Variants.lean` | For every ℓ with ℓ o e ≥ 0 whenever o ≥ 1 and e ≥ 0 (in particular every ℓ with `HY.LogOK ℓ`), real d ≥ 1, c ≥ 1 and c² ≥ 1 + 1/d: there is no `HY.NFO ℓ c d M n` (via `HL.stepO_cases`: every `HY.StepO ℓ` step is a `HY.Step` or `HY.SpeedLog` step, and `HL.no_drop_W`). |
| `HL.rpathW_last_T` | `Variants.lean` | For c ≥ 0: an `HL.RPathW c d` path (`RStep`, `Loose` and `Widen` steps) of length n ≥ 1 ending at `(P, T a')` has c · `HL.pin P` ≤ a' (its last step is `RStep.slow`, the only step producing a `T` kernel). `HL.pin` is the relaxed input superscript (0 on the empty prefix). Exact steps encode into such steps: `HY.Step` by `HL.sim` (c ≥ 0), `HY.StepO ℓ` (ℓ o e ≥ 0) by `HL.stepO_cases`, `HY.SpeedLog` by `HL.loose_of_speedLog`, `HY.Incl` by `HL.widen_of_incl`. |
| `HL.path_unwiden` | `Variants.lean` | Let R preserve `NN` (all entries ≥ 0) and, for all bl, a ≥ 0, a ≤ a₂, a ≤ e₂ and R `(bl, S a₂ e₂)` L₃, give some L' with R `(bl, T a)` L' and R L' L₃ (`HL.widen_dec` proves this for `RStep c d` with c ≥ 0, d ≥ 1). If every step of `M 0, …, M n` is an R-step or a `Widen` step, `NN (M 0)` and `M n = (bl, T a')`, there is an R-path `M' 0, …, M' n` with `M' 0 = M 0` and `M' n = M n`. So statements determined by the length and the two endpoints of a path transfer; statements about intermediate lines need not (from `([], T 1)` a `Widen` step reaches `([], S 1 1)`, which lowers the one-level potential from 1 to 0). |
| `HY.nfCheck_sound` | `Calculus.lean` | Acceptance by the tag-list checker `HY.nfCheck c d a0 ts` gives ∃ M n, `HY.NF c d M n`. |
| `HD.dagCheck_sound`, `HDS.dagCheck_sound` | `Dag.lean`, `DagStrict.lean` | Acceptance by the DAG checker gives ∃ M n, `HY.NF c d M n`; for `HDS`, also kernel time ≥ input superscript and `HDS.SpOK` on every line. |
| `HD.dagCheck_soundO`, `HDS.dagCheck_soundO` | `Dag.lean`, `DagStrict.lean` | The same for every ℓ with `HY.LogOK ℓ`: acceptance gives ∃ M n, `HY.NFO ℓ c d M n` (for `HDS` with the strict properties). `dagCheck_sound` is the case ℓ = max, `dagCheck_sound1` the case ℓ = 1. |
| `HL.sim` | `Relaxed.lean` | For c ≥ 0, every `HY.Step c d L L'` is an `HL.RStep c d (enc L) (enc L')`. |
| `HLM.absCheck_sound` | `AbsCheck.lean` | Acceptance by `HLM.absCheck c d θ₀ lv S` gives `HLM.Hyp` (the hypotheses of the multi-level potential, including the Lemma 7.1 condition for every word) for the data cast to ℝ. |
| `HLM.no_nf_of`, `HLM.no_nf_le_of` | `Potential.lean` | From `HLM.Hyp c₀ d θ₀ lv` and c₀ ≤ c: no `HY.NF c d M n`; and, if every θ (level 0 included) is > 1 and 1 < c₀, a₀ < a' along every `HY.Step c d` path of length ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')`. |
| `HLM.rstep_mono` | `Potential.lean` | For c₀ ≤ c, an `HL.RStep c d L L'` from a line with nonnegative entries is an `HL.RStep c₀ d L L'`. |
| `HY.slow_convMerge_A34`, `HY.slow_convMerge_A34O` | `Displays.lean` | For real d ≥ 0, c ≥ 1 with c − 1/(d+1) ≤ 1, any e, q and outer prefix `rest`: `HY.Step c d` (resp. `HY.StepO ℓ c d`, any ℓ) takes `(⟨!q, 0, 1⟩ :: ⟨q, 1, 1⟩ :: rest, S 1 e)` to `(⟨q, 1, 1⟩ :: rest, T c)` (Lemma 7.2) and that line to `(⟨q, 1, 1⟩ :: rest, S c (d/(d+1)))` (Lemma 7.1 merged, s = 1/(d+1)): the DTISP line after a slowdown in the proof of Williams's Theorem 7.5 (p. A:34; paper row D8). |
| `HY.path_S_ne_nil` | `Displays.lean` | Along a `HY.Step c d` path from `([], T a₀)`, every line with a DTISP kernel has a nonempty block list (so `speedNew` with `bl = []`, Speedup Rule 0, never applies). The hypothesis `M 0 = ([], T a₀)` is needed: from `([], S a e)` the statement fails at the first line. |
| `HY.path_S_space_nonneg`, `HY.path_S_space_nonnegO` | `Displays.lean` | For d ≥ 0, along a `HY.Step c d` (resp. `HY.StepO ℓ c d`) path from `([], T a₀)`, every line with a DTISP kernel `S a e` has 0 ≤ e. (`Step.slow` itself accepts an `S` kernel with any real e, so on arbitrary formal lines it is more permissive than Williams's Lemma 7.2, which has e ≥ 0.) |
| `HY.path_alt`, `HY.path_alt_incl` | `Displays.lean`, `Variants.lean` | Along a `HY.Step c d` path (resp. a path of `HY.Step c d` and `HY.Incl` steps) from `([], T a₀)`, every line alternates (`HY.step_alt`: every `Step` preserves alternation; `HY.Incl` keeps the prefix). |
| `HL.rstep_T_mono` | `Displays.lean` | For c ≥ 0, d ≥ 0 and 0 ≤ a ≤ a': every `HL.RStep c d (bl, T a') L'` gives `HL.RStep c d (bl, T a) L'` (Lemma 7.1 with s' = min(s, a); Lemma 7.2 with a smaller bound). So DTIME_d[n^a] ⊆ DTIME_d[n^{a'}] directly before a relaxed step is absorbed by that step (paper row D7). |
| `HL.cor78_base_reach` | `Displays.lean` | For every c and real d ≥ 0: `HL.RStep c d ([], T ((d+1)/(d+2))) ([1], S 1 0)` (`convN`, s = 0) and `HL.RStep c d ([1], S 1 0) ([1, 1], S 1 (d/(d+1)))` (`speedM`, x = 0): the base case of Corollary 7.8 as printed on p. A:34 (paper row D6), with omitted outputs read as 1, is two relaxed steps. |

## What the build does not check

Lean checks statements about the *formal* calculus. It does not check:

- that `HY.Step` is Williams's calculus (a modelling claim, compared rule by rule in Table 2 and Section 2.4 of `paper/paper.tex`, with the calibration of Section 2.5);
- that `HL.RStep` covers every move of that calculus beyond `HL.sim` (paper Section 6);
- the comparison of the formal rules with each displayed derivation step of Williams's §7 (paper Appendix A, checked at sample parameter values by `scripts/inventory.py` and `scripts/w13_25line.py`, which assert the outcomes and formulas stated there, under the output conventions listed there; the splice of Lemma 7.7's induction is argued on paper only);
- the scope of the ceilings. They are theorems about the formalised rule set (`HY.Step` with the extensions named in each theorem), which is our reading of Williams's lemmas as set out in paper Section 2.4. His proof sketches display some lines that differ from it (paper Section 2.4, Appendix A), and for some of those the ceilings are not established; for example, under the smaller output superscripts of the new log n block displayed in his sketch of Theorem 7.9 only the closed-form ceiling is proved (`HL.no_drop_W`, `HL.no_nfO`) and the sharp ceilings are not established in general, while the staircase proofs exist for every output between 1 and max(o, e) (`conjecture_fails_O`). The scope table at the end of paper Section 2.4 is the one full statement of what is covered and how (an exact step; a single relaxed step, one `HL.RStep` or `HL.Widen` step, covered by the relaxed ceilings; a single `HL.Loose` step, covered by the relaxed closed-form ceiling `HL.qf_ge_W` only; or an expansion into several steps); we do not claim its list is exhaustive;
- the replays of Williams's printed 25-line proof and of his other displays (`scripts/w13_25line.py`, `scripts/inventory.py`): the exact replay of the 25-line proof satisfies the formal rules, while several printed transitions, read literally, are steps of no rule (paper rows D1, D2; each gap at most 3·10⁻⁹); the numerical origin is not determined;
- the soundness of Williams's lemmas (Lemmas 7.1, 7.2, 7.3, Lemma 3.3 inside a prefix, the combining of same-type blocks of his §2, Theorem 3.1 with Corollary 3.2), on which the complexity reading SAT ∉ DTIME_d[n^c] for c below the lower values depends, as Williams's Theorem 7.5 does (paper Section 8);
- the staircase recursion and its boundary c*_stair (its digits are numerical estimates that assume the recursion's verdict is monotone in c), and the conjecture that the threshold of the calculus equals c*_stair (paper Section 7). The exact threshold is open.

The scripts in [`scripts/`](scripts/) re-check the certificates and the ceiling data in exact rationals, replay the 39-line proof (also with outputs 1, max(o, 1) and max(1, e) for the new log n block) and Williams's printed 25-line proof from Williams's text, replay the displayed derivations of Williams's §7 against the formal rules at the sample parameters and outputs listed in paper Appendix A (`inventory.py`; the splice of Lemma 7.7's induction is a paper argument, and Corollary 7.8, which Williams does not display as a derivation, is checked by constructing one at the specified samples), and compute the numbers of paper Section 7; see [`scripts/README.md`](scripts/README.md). They are not part of the kernel-checked results.
