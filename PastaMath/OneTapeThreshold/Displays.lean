-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The DTISP line after a slowdown in the proof of Williams's Theorem 7.5 (p. A:34)

After the first use of Corollary 7.8 the proof of Theorem 7.5 reaches
`(∃ n^G)(∀ n)(∃ log n) DTISP[n, n^{d/(d+1)}]` and prints the next line as
`(∃ n^G)(∀ n) DTISP[n^c, n^{d/(d+1)}]`. `slow_convMerge_A34` derives that line in two exact steps:
Lemma 7.2 (`Step.slow`) removes the log n block and leaves `(∀ n^1)^1 DTIME_d[n^c]`, and Lemma 7.1
merged into the universal block (`Step.convMerge`) with s = 1/(d+1) gives
`(∀ n^1)^1 DTISP[n^c, n^{d/(d+1)}]`. The universal block keeps guess and output exactly 1 because
c − 1/(d+1) ≤ 1, which holds for Williams's range 1 ≤ c < (d+2)/(d+1). The outer prefix `rest` and
the space exponent `e` of the starting kernel are arbitrary.

`step_S_ne_nil`, `path_S_ne_nil`: every `Step` that produces a DTISP kernel produces a nonempty block list,
so along a `Step` path from `([], T a₀)` no line is a quantifier-free DTISP class, and `Step.speedNew` with
`bl = []` (Lemma 3.3 on a quantifier-free DTISP class, Speedup Rule 0) never applies on such a path.
-/

namespace PastaMath.OneTapeThreshold
namespace HY

theorem slow_convMerge_A34O (ℓ : ℝ → ℝ → ℝ) (c d e : ℝ) (q : Bool) (rest : List Blk) (hd : 0 ≤ d)
    (hc : 1 ≤ c) (hcd : c - 1 / (d + 1) ≤ 1) :
    StepO ℓ c d (⟨!q, 0, 1⟩ :: ⟨q, 1, 1⟩ :: rest, .S 1 e) (⟨q, 1, 1⟩ :: rest, .T c) ∧
      StepO ℓ c d (⟨q, 1, 1⟩ :: rest, .T c) (⟨q, 1, 1⟩ :: rest, .S c (d / (d + 1))) := by
  have hd1 : 0 < d + 1 := by linarith
  refine ⟨?_, ?_⟩
  · have h := StepO.slow (ℓ := ℓ) (c := c) (d := d) ⟨!q, 0, 1⟩ (⟨q, 1, 1⟩ :: rest) (.S 1 e)
      le_rfl le_rfl le_rfl le_rfl
    have hm : c * max (max (pin (⟨q, 1, 1⟩ :: rest)) (1 : ℝ)) (max 0 (Ker.S 1 e).time) = c := by
      simp only [pin, Ker.time, max_self, max_eq_right (zero_le_one' ℝ), mul_one]
    dsimp only at h
    rw [hm] at h
    exact h
  · have hs : 0 < 1 / (d + 1) := one_div_pos.mpr hd1
    have hs1 : 1 / (d + 1) ≤ c := le_trans ((div_le_one hd1).mpr (by linarith)) hc
    have h := StepO.convMerge (ℓ := ℓ) (c := c) (d := d) ⟨q, 1, 1⟩ rest c (1 / (d + 1)) hs hs1 le_rfl
    have e1 : max (1 : ℝ) (c - 1 / (d + 1)) = 1 := max_eq_left hcd
    have e2 : max (c - 1 / (d + 1)) (1 : ℝ) = 1 := max_eq_right hcd
    have e3 : d * (1 / (d + 1)) = d / (d + 1) := by ring
    dsimp only at h
    rw [e1, e2, e3] at h
    exact h

/-- The two steps of the module docstring in `Step`: Lemma 7.2 then Lemma 7.1 merged with
s = 1/(d+1), under any outer prefix `rest`, for 0 ≤ d, 1 ≤ c and c − 1/(d+1) ≤ 1. -/
theorem slow_convMerge_A34 (c d e : ℝ) (q : Bool) (rest : List Blk) (hd : 0 ≤ d) (hc : 1 ≤ c)
    (hcd : c - 1 / (d + 1) ≤ 1) :
    Step c d (⟨!q, 0, 1⟩ :: ⟨q, 1, 1⟩ :: rest, .S 1 e) (⟨q, 1, 1⟩ :: rest, .T c) ∧
      Step c d (⟨q, 1, 1⟩ :: rest, .T c) (⟨q, 1, 1⟩ :: rest, .S c (d / (d + 1))) :=
  let h := slow_convMerge_A34O max c d e q rest hd hc hcd
  ⟨step_of_stepO_max h.1, step_of_stepO_max h.2⟩

theorem step_S_ne_nil {c d : ℝ} {L L' : Line} (h : Step c d L L') {a e : ℝ} (hk : L'.2 = .S a e) :
    L'.1 ≠ [] := by
  cases h <;> simp_all

theorem path_S_ne_nil {c d a₀ : ℝ} {M : ℕ → Line} {n : ℕ} (hp : Path (Step c d) M n)
    (h0 : M 0 = ([], .T a₀)) : ∀ i ≤ n, ∀ a e : ℝ, (M i).2 = .S a e → (M i).1 ≠ [] := by
  intro i hi a e hk
  cases i with
  | zero => rw [h0] at hk; cases hk
  | succ j => exact step_S_ne_nil (hp j (by omega)) hk

end HY
end PastaMath.OneTapeThreshold
