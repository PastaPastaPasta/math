# Verifying the SAT-barriers result

## Build

Requirements: [elan](https://github.com/leanprover/elan) (installs Lean 4.31.0 pinned in `lean-toolchain`) and `git`. From the repository root:

```sh
lake exe cache get   # download prebuilt Mathlib (pinned in lake-manifest.json)
lake build           # builds PastaMath, including PastaMath/SatBarriers/Axioms.lean
```

To build and print axioms for this result alone:

```sh
lake build PastaMath.SatBarriers.Axioms
lake env lean PastaMath/SatBarriers/Axioms.lean
```

The build must finish with `Build completed successfully` and no errors or warnings.

## Expected axioms output

Every headline theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. Recorded output (Lean 4.31.0, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`):

```
'PastaMath.SatBarriers.cub_r7' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.cub_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.bw_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.e1beta_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation_rule2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation_loc' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation_locB' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.beta_half_beats_r7' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation_locT' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation_locX' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation_locU' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation_locU_r7' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_refutation_locC' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.locs_embed' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.no_locs_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.lv_locs_refutes' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.PR.proto_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.PR.no_refutation_proto' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.PR.proto_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.BS.der_der' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.BS.no_refutation_der' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.BS.derived_kappa' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.BS.derived_ns' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.BS.derived_kappa_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.AU.no_refutation_nonstrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.AU.no_refutation_locX_nonstrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.AU.derived_ns_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.AU.derived_ns_single_use' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.SatBarriers.AU.lv_refutesNS' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Headline declarations

| Declaration | File | Content |
|---|---|---|
| `cub_r7`, `cub_eq_zero_iff` | `Cubic.lean` | Characterises `r7 = 2cos(π/7)` as the unique root of `c³ − c² − 2c + 1 = 0` in `[1, ∞)`. |
| `bw_limit`, `no_refutation`, `e1beta_limit` | `Derivation.lean` | Buss–Williams limit and weakened `β ≥ β*` slowdown envelopes. |
| `no_refutation2` | `Derivation2.lean` | Two-flag slowdown envelope (`β₁ ≥ β*`, `β₂ ≥ β_non`). |
| `no_refutation_rule2` | `Rule2.lean` | Two-step transitions (`Rule2Step`) do not pass `r7`. |
| `no_refutation_loc`, `no_refutation_locB`, `beta_half_beats_r7` | `Localized.lean`, `LocalizedBeta.lean` | Localized `β`-envelope threshold `(1 − β)(c − 1)² ≤ cub c` and sharpness at `β = 1/2`. |
| `no_refutation_locT`, `no_refutation_locX`, `no_refutation_locU`, `no_refutation_locC` | `LocalizedTrace.lean`..`LocalizedCopy.lean` | Trace speedups, max-envelope, unconditional exponent-0 removal, and free-kernel trace steps. |
| `locs_embed`, `no_locs_refutation`, `lv_locs_refutes` | `LocsEmbed.lean` | Sound embedding of concrete array-exponent semantics into `LStepX c 1`. |
| `PR.proto_path`, `PR.no_refutation_proto`, `PR.proto_witness` | `Protocol.lean` | Multi-round public-coin protocol steps expand into `Step` paths and stay capped at `r7`. |
| `BS.der_der`, `BS.no_refutation_der`, `BS.derived_kappa`, `BS.derived_ns`, `BS.derived_kappa_sharp` | `Bootstrap.lean` | Inductive closure `Der` adds nothing for `c ≥ r7`; derived inclusion bounds and sharpness. |
| `AU.no_refutation_nonstrict`, `AU.no_refutation_locX_nonstrict`, `AU.derived_ns_lower`, `AU.lv_refutesNS` | `Audit.lean` | Non-strict refutations (`a' ≤ a₀`) excluded; strict `τ₀(c)·a < v` lower bound for derived single-block inclusions. |

## What the build does not check

Lean checks all theorems about the formalised rule systems unconditionally. It does not check the complexity-theoretic soundness of concrete speedup/slowdown lemmas or informal claims about whether external complexity techniques fall inside these formal rule families.
