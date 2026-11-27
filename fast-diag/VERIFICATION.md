# Verifying the `fast-diag` combinatorial core

## Build

Requirements: [elan](https://github.com/leanprover/elan) (installs Lean 4.31.0 pinned in `lean-toolchain`) and `git`. From the repository root:

```sh
lake exe cache get   # download prebuilt Mathlib (pinned in lake-manifest.json)
lake build           # builds PastaMath, including PastaMath/FastDiag/Axioms.lean
```

To build and print axioms for this result alone:

```sh
lake build PastaMath.FastDiag.Axioms
lake env lean PastaMath/FastDiag/Axioms.lean
```

The build must finish with `Build completed successfully` and no errors or warnings.

## Expected axioms output

Every headline theorem depends only on a subset of the standard axioms `propext`, `Classical.choice`, and `Quot.sound` (`corr_self` needs only `propext` and `Quot.sound`). Recorded output (Lean 4.31.0, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`):

```
'PastaMath.FastDiag.even_tuples_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.sum_tables_prod_sgn' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.corr_self' depends on axioms: [propext, Quot.sound]
'PastaMath.FastDiag.corr_pow_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.potential_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.potential_ge_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.exists_hard_of_potential' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.sgn_blockXor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.blockXor_sign_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.blockGood_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.exists_hard_blockXor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.sum_partial_table_prod_sgn' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.blockXor_partial_sign_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.blocks_le_of_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.potential_params_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.exists_hard_blockXor_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.expected_potential_lt_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.card_filter_mem_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.regular_bipartite_coloring' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.perm_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.clos_rearrangeable' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.sqrt_saving_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.sqrt_saving_superlinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.ew_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.FastDiag.ew_threshold_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Headline declarations

| Declaration | File | Content |
|---|---|---|
| `even_tuples_card_le`, `blockGood_card_le` | `Moment.lean` | Even-occurrence word count `≤ k^{2k} · card(α)^k` and block-even tuple bound. |
| `corr_self`, `corr_pow_expand`, `potential_ge_count`, `potential_sum_le`, `exists_hard_of_potential` | `Moment.lean` | Correlation expansion and moment-potential lower/upper bounds. |
| `sgn_blockXor`, `blockXor_sign_sum`, `sum_partial_table_prod_sgn`, `blockXor_partial_sign_sum`, `exists_hard_blockXor` | `Moment.lean` | Block-XOR sign-sum identities (empty and partial assignments) and hard-function existence. |
| `blocks_le_of_ratio`, `potential_params_lt`, `exists_hard_blockXor_of_params`, `expected_potential_lt_of_params` | `Params.lean` | Integer parameter inequality giving `E_∅ Φ_m < 1`. |
| `regular_bipartite_coloring`, `clos_rearrangeable` | `Clos.lean` | König's edge-colouring theorem (from Hall) and 3-stage Clos rearrangeability. |
| `sqrt_saving_linear`, `sqrt_saving_superlinear`, `ew_threshold`, `ew_threshold_sharp` | `Arith.lean` | `√log` exponent arithmetic for the tableau verifier in Corollaries B and B_λ. |

## Parameter script

From `fast-diag/scripts/`:

```sh
python3 params.py
```

## What the build does not check

Lean checks only the unconditional combinatorial and arithmetic core above. It does **not** check the fan-out-3 normal form (Lemma 8), the bipartite tensor network and running-time analysis (Section 5), the tableau machine construction (Section 6), the threshold/relativisation outlines (Section 7), or the external October 2026 network-contraction and `#3`-CNF theorems (OpenAI Thm D.1; Anthropic Lemma 8, Thm A(a),(b), Thm B, Main Theorem, which are AI-written and have not been human-refereed).
