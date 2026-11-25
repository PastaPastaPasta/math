-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Proof39
import PastaMath.OneTapeThreshold.Ceiling
import PastaMath.OneTapeThreshold.StairD1
import PastaMath.OneTapeThreshold.StairD2
import PastaMath.OneTapeThreshold.StairD3

/-!
# Williams's §7 calculus as formalised: the conjecture fails, and the threshold lies in a short interval

* `conjecture_fails`: for (d, c) = (1, 1.30921174), (2, 1.1915968), (3, 1.1386523) there is a strict
  normal-form proof `HY.NF c d` all of whose lines have kernel time ≥ input superscript and, on DTISP
  kernels, space ≤ time, and every real root of Williams's p_d is below c.
* `threshold_bounds`: for the same (d, c_d) a strict normal-form proof exists at c_d, and for every
  real c ≥ 1.3094 (d = 1), c ≥ 1.192 (d = 2), c ≥ 1.1392 (d = 3) none exists. So
  sup{c : ∃ M n, HY.NF c d M n} lies in [1.30921174, 1.3094], [1.1915968, 1.192] and
  [1.1386523, 1.1392]. The non-strict and relaxed forms of the upper bounds, for paths from
  `([], T a₀)` with a₀ > 0, are `HLM.ceiling_d1`, `HLM.ceiling_d2` and `HLM.ceiling_d3`; with the inclusion
  DTIME_d[t] ⊆ DTISP[t, t] added, `HLM.ceilingX_d1`, `HLM.ceilingX_d2` and `HLM.ceilingX_d3`.
  All of them are for the output max(b, e) of the new log n block of Lemma 3.3 and for Lemma 7.2 with
  its full maximum (including the output of the remaining prefix).
* `conjecture_fails_one`: the existence part of `conjecture_fails` in the calculus in which that
  block has output exactly 1 (`HY.NFO (fun _ _ => 1)`), from the same certificate checks.
* `conjecture_fails_O`: the same for every output ℓ with `HY.LogOK ℓ` (1 ≤ ℓ(o, e) ≤ max(o, e) for
  o ≥ 1, e ≥ 0); `conjecture_fails_in` is the case ℓ(o, e) = max(o, 1), the input superscript o of the
  kernel (the display of Case 1 of Williams's sketch of Theorem 7.9), and `conjecture_fails_sp` the case
  ℓ(o, e) = max(1, e) (the output that Lemma 3.3 states for a quantifier-free class).
-/

namespace PastaMath.OneTapeThreshold

open HY

/-- For d = 1, 2, 3 and c = 130921174/100000000, 11915968/10000000, 11386523/10000000 respectively:
there is a strict normal-form proof `HY.NF c d M n` with kernel time ≥ input superscript and, on
DTISP kernels, space ≤ time on every line `M i`, i ≤ n; and every real root x of `pd d` satisfies
x < c. -/
theorem conjecture_fails :
    ((∃ M n, NF (130921174 / 100000000 : ℝ) 1 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
      ∀ x : ℝ, pd 1 x = 0 → x < 130921174 / 100000000) ∧
    ((∃ M n, NF (11915968 / 10000000 : ℝ) 2 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
      ∀ x : ℝ, pd 2 x = 0 → x < 11915968 / 10000000) ∧
    ((∃ M n, NF (11386523 / 10000000 : ℝ) 3 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
      ∀ x : ℝ, pd 3 x = 0 → x < 11386523 / 10000000) := by
  refine ⟨⟨HStair.stairD1_snf, fun x h => ?_⟩, ⟨HStair.stairD2_snf, fun x h => ?_⟩,
    ⟨HStair.stairD3_snf, fun x h => ?_⟩⟩
  · have := pd1_root_lt h; linarith
  · have := pd2_root_lt h; linarith
  · have := pd3_root_lt h; linarith

/-- For each d = 1, 2, 3: a strict normal-form proof `HY.NF c_d d` exists at
c_d = 130921174/100000000, 11915968/10000000, 11386523/10000000 respectively, and for every real
c ≥ 6547/5000, 149/125, 712/625 respectively there is no strict normal-form proof `HY.NF c d M n`. -/
theorem threshold_bounds :
    ((∃ M n, NF (130921174 / 100000000 : ℝ) 1 M n) ∧
      ∀ c : ℝ, 6547 / 5000 ≤ c → ∀ M n, ¬ NF c 1 M n) ∧
    ((∃ M n, NF (11915968 / 10000000 : ℝ) 2 M n) ∧
      ∀ c : ℝ, 149 / 125 ≤ c → ∀ M n, ¬ NF c 2 M n) ∧
    ((∃ M n, NF (11386523 / 10000000 : ℝ) 3 M n) ∧
      ∀ c : ℝ, 712 / 625 ≤ c → ∀ M n, ¬ NF c 3 M n) :=
  ⟨⟨HStair.stairD1_nf, fun _ hc => (HLM.ceiling_d1 hc).1⟩,
    ⟨HStair.stairD2_nf, fun _ hc => (HLM.ceiling_d2 hc).1⟩,
    ⟨HStair.stairD3_nf, fun _ hc => (HLM.ceiling_d3 hc).1⟩⟩

/-- For d = 1, 2, 3 and c = 130921174/100000000, 11915968/10000000, 11386523/10000000 respectively:
in the calculus `HY.StepO (fun _ _ => 1)`, in which the new log n block of Lemma 3.3 has output
exactly 1, there is a strict normal-form proof `HY.NFO (fun _ _ => 1) c d M n` with kernel time ≥
input superscript and, on DTISP kernels, space ≤ time on every line `M i`, i ≤ n. -/
theorem conjecture_fails_one :
    (∃ M n, NFO (fun _ _ => 1) (130921174 / 100000000 : ℝ) 1 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
    (∃ M n, NFO (fun _ _ => 1) (11915968 / 10000000 : ℝ) 2 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
    (∃ M n, NFO (fun _ _ => 1) (11386523 / 10000000 : ℝ) 3 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) :=
  ⟨HStair.stairD1_snf1, HStair.stairD2_snf1, HStair.stairD3_snf1⟩

/-- For every log n output ℓ with `LogOK ℓ` and d = 1, 2, 3, c = 130921174/100000000,
11915968/10000000, 11386523/10000000 respectively: in `HY.StepO ℓ` there is a strict normal-form proof
`HY.NFO ℓ c d M n` with kernel time ≥ input superscript and, on DTISP kernels, space ≤ time on every line
`M i`, i ≤ n. -/
theorem conjecture_fails_O {ℓ : ℝ → ℝ → ℝ} (hℓ : LogOK ℓ) :
    (∃ M n, NFO ℓ (130921174 / 100000000 : ℝ) 1 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
    (∃ M n, NFO ℓ (11915968 / 10000000 : ℝ) 2 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
    (∃ M n, NFO ℓ (11386523 / 10000000 : ℝ) 3 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) :=
  ⟨HStair.stairD1_snfO hℓ, HStair.stairD2_snfO hℓ, HStair.stairD3_snfO hℓ⟩

/-- `conjecture_fails_O` for ℓ(o, e) = max(o, 1): the new log n block of Lemma 3.3 gets the input
superscript of the kernel, as displayed in Case 1 of Williams's sketch of Theorem 7.9 (p. A:37). -/
theorem conjecture_fails_in :
    (∃ M n, NFO (fun o _ => max o 1) (130921174 / 100000000 : ℝ) 1 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
    (∃ M n, NFO (fun o _ => max o 1) (11915968 / 10000000 : ℝ) 2 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
    (∃ M n, NFO (fun o _ => max o 1) (11386523 / 10000000 : ℝ) 3 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) :=
  conjecture_fails_O logOK_in

/-- `conjecture_fails_O` for ℓ(o, e) = max(1, e): the new log n block of Lemma 3.3 gets the output that
Lemma 3.3 states for a quantifier-free DTISP class. -/
theorem conjecture_fails_sp :
    (∃ M n, NFO (fun _ e => max 1 e) (130921174 / 100000000 : ℝ) 1 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
    (∃ M n, NFO (fun _ e => max 1 e) (11915968 / 10000000 : ℝ) 2 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) ∧
    (∃ M n, NFO (fun _ e => max 1 e) (11386523 / 10000000 : ℝ) 3 M n ∧
        ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ HDS.SpOK (M i).2) :=
  conjecture_fails_O logOK_sp

end PastaMath.OneTapeThreshold
