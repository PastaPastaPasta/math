-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Proof39
import PastaMath.OneTapeThreshold.Ceiling
import PastaMath.OneTapeThreshold.StairD1
import PastaMath.OneTapeThreshold.StairD2
import PastaMath.OneTapeThreshold.StairD3

/-!
# Williams's §7 calculus: the conjecture fails, and the threshold lies in a short interval

* `conjecture_fails`: for (d, c) = (1, 1.30921174), (2, 1.1915968), (3, 1.1386523) there is a strict
  normal-form proof `HY.NF c d` all of whose lines have kernel time ≥ input superscript and, on DTISP
  kernels, space ≤ time, and every real root of Williams's p_d is below c.
* `threshold_bounds`: for the same (d, c_d) a strict normal-form proof exists at c_d, and for every
  real c ≥ 1.3094 (d = 1), c ≥ 1.192 (d = 2), c ≥ 1.1392 (d = 3) none exists. So
  sup{c : ∃ M n, HY.NF c d M n} lies in [1.30921174, 1.3094], [1.1915968, 1.192] and
  [1.1386523, 1.1392]. The non-strict and relaxed forms of the upper bounds are
  `HLM.ceiling_d1`, `HLM.ceiling_d2` and `HLM.ceiling_d3`.
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

end PastaMath.OneTapeThreshold
