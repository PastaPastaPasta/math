# Verifying the two-cut rank and sum-of-squares results

## Build

Requirements: [elan](https://github.com/leanprover/elan) (installs Lean 4.31.0 pinned in `lean-toolchain`) and `git`. From the repository root:

```sh
lake exe cache get   # download prebuilt Mathlib (pinned in lake-manifest.json)
lake build           # builds PastaMath, including PastaMath/TwoCutSoS/Axioms.lean
```

The build must end with `Build completed successfully` and no errors. To print the axioms of every headline theorem on its own:

```sh
lake env lean PastaMath/TwoCutSoS/Axioms.lean
```

## Expected axioms output

Every headline theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (the standard axioms of Lean's logic as used by Mathlib). Output recorded on Lean 4.31.0, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`:

```
'PastaMath.TwoCutSoS.sameBiquad_iff_qf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.sameBiquad_iff_sym4' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.hasPTRank_iff_hasTwoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.prod_of_twoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.twoCut_of_sos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.twoCut_of_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.sos_of_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.sos_of_twoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.sos_of_ptRank' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.crossing_prod_of_twoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.crossing_twoCut_of_sos' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.crossing_twoCut_of_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.crossing_sos_of_twoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.rz_lemma313_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.rzM1_hasSoS_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.rz_prop316_left_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.rzM2_hasSoS_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.rz_prop316_right_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.twoCut_ge_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.twoCut_gt_max_of_ge_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.twoCut_two_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.transpose_twoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.twoCut_three_three_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.clifford_twoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.exact_of_border_coeffs' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.tc45_twoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.tc46_twoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.tc88_twoCut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.border44_identity_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.border44_rank_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.border44_laurent_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.reflOp_involutive' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.reflOp_selfadjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.wordPoly_eval_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.reflection_slice_constraint' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.valuation_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.layer_grouping_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.CertPacking.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.CertPacking.asymptotic_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.packing_K4_quarter_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.TwoCutSoS.reflection_wordSpan_nogo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The Lean files contain no `sorry`, `admit`, `native_decide`, `implemented_by`, or custom `axiom` declarations, and no umbrella `import Mathlib.Tactic`. The CI workflow (`.github/workflows/lean.yml`) checks these constraints and the axioms output on every push to `main`, on pull requests, and on manual `workflow_dispatch`.

## Headline theorems

All names are in namespace `PastaMath.TwoCutSoS`.

| Theorem | File | Plain-language meaning |
|---|---|---|
| `sameBiquad_iff_qf`, `sameBiquad_iff_sym4` | `Defs.lean` | Exact monomial-coefficient equivalence (`SameBiquad`) equals pointwise `Q_M = Q_N` over *every* field (including char `2`), and equals `sym4 M = sym4 N` whenever `char K ≠ 2`. |
| `hasPTRank_iff_hasTwoCut` | `Dictionary.lean` | Over every field `K`, `HasPTRank M c ↔ HasTwoCut M c`. |
| `prod_of_twoCut`, `twoCut_of_sos`, `twoCut_of_prod`, `sos_of_prod`, `sos_of_twoCut`, `sos_of_ptRank` | `Dictionary.lean` | Exact dictionary: `Prod ≤ TC` (every field); `TC ≤ 2 SoS` and `TC ≤ 4 Prod` (`char K ≠ 2`, fully symmetric `M`); `SoS ≤ 2 Prod ≤ 2 TC = 2 PT-rank` (`char K ≠ 2`, `√(-1) ∈ K`). |
| `crossing_prod_of_twoCut`, `crossing_twoCut_of_sos`, `crossing_twoCut_of_prod`, `crossing_sos_of_twoCut` | `Dictionary.lean` | Specialisation of the dictionary to the Hurwitz biquadratic form `X_{r,s}` (`M = 1`, which is fully symmetric). |
| `rz_lemma313_counterexample`, `rzM1_hasSoS_two` | `RossmanZhu.lean` | `M₁ = E_{(0,0),(0,1)}` has `PT-rank = 1` and `SoS > 1` (`= 2` when `√(-1) ∈ K`) over every field of `char ≠ 2`, refuting Rossman–Zhu Lemma 3.13. |
| `rz_prop316_left_counterexample`, `rzM2_hasSoS_four` | `RossmanZhu.lean` | `M₂ = E_{(0,0),(0,1)} + E_{(1,2),(1,3)}` has `PT-rank ≤ 2` and `SoS > 3` (`= 4` when `√(-1) ∈ K`) over every field of `char ≠ 2`, refuting the left inequality of Rossman–Zhu Prop. 3.16. |
| `rz_prop316_right_counterexample` | `RossmanZhu.lean` | `M₃ = E_{(0,0),(0,1)} - E_{(0,1),(0,0)}` has `SoS = 0` and `PT-rank ≥ 1` over every field of `char ≠ 2`, refuting the right inequality of Rossman–Zhu Prop. 3.16. |
| `twoCut_ge_max` | `LowerBounds.lean` | `TC_K(r, s) ≥ max(r, s)` for all `0 < r` and `0 < s`, over every field `K` (including char 2). |
| `twoCut_gt_max_of_ge_three` | `LowerBounds.lean` | `TC_K(r, s) ≥ max(r, s) + 1` for all `r, s ≥ 3` over every field `K` (including char 2). |
| `twoCut_two_iff` | `LowerBounds.lean` | `TC_K(2, s) = 2⌈s/2⌉` for all `s ≥ 1` over every field `K`. |
| `transpose_twoCut` | `LowerBounds.lean` | `TC_K(r, s) ≤ 1 + r*s - m*(m+1)/2` (`m = min r s`) over every field `K`. |
| `twoCut_three_three_iff` | `LowerBounds.lean` | `TC_K(3, 3) = 4` over every field `K`. |
| `clifford_twoCut` | `Witnesses.lean` | `n` anticommuting involutions in `M_d(K)` give `TC_K(d, n) ≤ 2d` (`char K ≠ 2`). |
| `exact_of_border_coeffs` | `Witnesses.lean` | A pole-order-`k` border two-cut decomposition of `I_{rs}` of ranks `a + b` gives `TC_K(r, s) ≤ (k + 1) * (a + b)` over every field `K`. |
| `tc45_twoCut`, `tc46_twoCut`, `tc88_twoCut` | `Witnesses.lean` | Explicit `±1` schemes proving `TC_K(4,5) ≤ 8`, `TC_K(4,6) ≤ 8`, and `TC_K(8,8) ≤ 16` over every field `K`. |
| `border44_rank_le`, `border44_laurent_identity`, `border44_identity_field` | `Witnesses.lean` | Explicit width-3 integer polynomial families `b44A_eval ε, b44B_eval ε` with `rank ≤ 3` each and `b44A_eval ε + (b44B_eval ε)^Γ = ε² I₁₆ + ε³ R₁ + ε⁴ R₂` over every field `K` (`bTC_{K,2}(4,4) ≤ 6`). |
| `reflOp_involutive`, `reflOp_selfadjoint`, `wordPoly_eval_B` | `ReflectionPowers.lean` | `T_{-1} = E_1(p)^{⊗K}` is an involution and self-adjoint in `L²(μ_p)`, and a polynomial `P(B_0, …, B_{K-1})` in `B_i = A_i^Γ` acts diagonally in the `T_{-1}` eigenbasis via `wordPolyEval`. |
| `reflection_slice_constraint` | `ReflectionPowers.lean` | Every exact reflection-type decomposition over `ℝ` satisfies `max r s ≤ 2 * min n (r * s - n)`. |
| `valuation_theorem`, `layer_grouping_le` | `ReflectionPowers.lean` | When `λ = a/b` has a prime `ℓ ∣ (a - b)` with `ℓ ∤ a`, every `ℤ_(ℓ)`-coefficient word span costs at least `∑_T min(μ_p(T), μ_{1-p}(T))`, attained exactly by the layer grouping at every `K`. |
| `CertPacking.lower_bound`, `CertPacking.asymptotic_bound` | `ReflectionPowers.lean` | Farkas certificate packings lower-bound `wordSpanCost` and tensorise supermultiplicatively across block lengths. |
| `packing_K4_quarter_value` | `ReflectionPowers.lean` | Pure-kernel-checked 22-certificate `K = 4, p = 1/4` rational packing of exact value `57/256`. |
| `reflection_wordSpan_nogo` | `ReflectionPowers.lean` | For every shape `r, s ≥ 2` and every reflection-type multiplicity satisfying the slice constraint, word-span tensor powers have asymptotic rate strictly above `√(1 + q²)`. |

## What the build does not check

- `reflection_wordSpan_nogo` bounds the normalised word-span cost `D^K * wordSpanCost p h`. The linear-algebraic bridge identifying this quantity with the matrix two-cut cost of word-span decompositions of diagonalisable reflection-type bases over `ℝ` (simultaneous diagonalisation of Kronecker powers `A^{⊗K}` and `B^{⊗K}` by the eigenbasis of `T_{-1}` in `L²(μ_p)`) is proved on paper in Section 5.1; `wordPoly_eval_B` checks the algebraic eigenvalue formula inside the `L²(μ_p)` model. The no-go theorem does not cover decompositions outside the word algebra, non-reflection spectra, non-diagonalisable bases, or border families.
- Whether `SoS_ℂ(Q_M) ≤ PT-rank_ℂ(M)` holds for *fully symmetric* matrices `M` remains open; the counterexamples `M₁, M₂, M₃` are non-fully-symmetric matrices refuting the printed statements of Rossman–Zhu (arXiv:2512.01227v1) Lemma 3.13 and Proposition 3.16.
