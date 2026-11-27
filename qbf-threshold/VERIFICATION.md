# Verifying the QBF_k-threshold result

## Build

Requirements: [elan](https://github.com/leanprover/elan) (installs Lean 4.31.0 pinned in `lean-toolchain`) and `git`. From the repository root:

```sh
lake exe cache get   # download prebuilt Mathlib (pinned in lake-manifest.json)
lake build           # builds PastaMath, including PastaMath/QbfThreshold/Axioms.lean
```

To build and print axioms for this result alone:

```sh
lake build PastaMath.QbfThreshold.Axioms
lake env lean PastaMath/QbfThreshold/Axioms.lean
```

The build must finish with `Build completed successfully` and no errors or warnings.

## Expected axioms output

Every headline theorem depends only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound` (`decide +kernel` adds no axiom). Recorded output (Lean 4.31.0, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`):

```
'PastaMath.QbfThreshold.key' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.step_pot' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.no_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.no_refutation_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.no_refutation_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.exists_par' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.ge_of_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.qbf_no_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.qbf_no_refutation_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.qbf_no_refutation_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.par_one_eq_r7' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.sat_no_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.checkL_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.qcert1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.qcert2_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.qcert3_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.qcert4_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.interval_k1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.interval_k2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.interval_k3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.interval_k4' depends on axioms: [propext, Classical.choice, Quot.sound]
'PastaMath.QbfThreshold.cert_below' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Headline declarations

| Declaration | File | Content |
|---|---|---|
| `key`, `step_pot` | `Calculus.lean` | Core inequality and step monotonicity of the grouping potential `val`. |
| `exists_par`, `ge_of_poly` | `Threshold.lean` | Existence of threshold parameter `Par` for every `k ≥ 1` and comparison with `c³/k − c² − 2c + k ≥ 0`. |
| `qbf_no_refutation`, `qbf_no_refutation_reach` | `Threshold.lean`, `Summary.lean` | No strict refutation in `QStep c k` for `c > k` with `c³/k − c² − 2c + k ≥ 0`. |
| `qbf_no_refutation_strict` | `Threshold.lean` | No non-strict refutation (`a' ≤ a₀`, `a₀ > 0`, `n ≥ 1`) when `c³/k − c² − 2c + k > 0`. |
| `par_one_eq_r7`, `sat_no_refutation` | `Threshold.lean` | At `k = 1`, `P.c = 2cos(π/7)` and SAT-versus-DTS has no refutation for `c ≥ 2cos(π/7)`. |
| `checkL_sound` | `CertDefs.lean` | Any literal proof accepted by the rational checker `checkL` embeds into a strict `QStep` refutation. |
| `qcert1_ok` .. `qcert4_ok` | `Cert.lean` | Four literal refutation certificates (`k = 1..4`) checked with `decide +kernel`. |
| `interval_k1` .. `interval_k4`, `cert_below` | `Summary.lean` | Certified threshold intervals for `k = 1..4` and strict inequality below Williams's roots. |

## Independent script check

From `qbf-threshold/scripts/`:

```sh
python3 qbf_check.py cert_k1.json cert_k2.json cert_k3.json cert_k4.json
```

## What the build does not check

Lean checks the theorems about the formal calculus `QStep` and the rational literal checker `checkL`. It does not check that `checkL` matches Williams's prose description in TOCT 2013 §5 (a modelling claim discussed in Section 2 of the paper), Williams's general parametric family achieving every `c < c_k`, or the soundness of the underlying complexity-theoretic simulation lemmas.
