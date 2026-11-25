-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Relaxed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
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

`step_S_space_nonneg`, `path_S_space_nonneg`: for d ≥ 0 every `Step` that produces a DTISP kernel
produces a space exponent ≥ 0, so along a `Step` path from `([], T a₀)` every DTISP line has space ≥ 0
(`Step.slow` itself accepts a DTISP kernel with any real space exponent); `step_S_space_nonnegO`,
`path_S_space_nonnegO` are the same for `StepO ℓ`.

`HL.cor78_base_reach`: the right-hand side of the base case of Corollary 7.8 as printed on p. A:34,
`(∃ n)(∀ log n) DTISP[n, n^{d/(d+1)}]` from `DTIME_d[n^{(d+1)/(d+2)}]`, is reached in the relaxed
calculus by two steps, for every c and d ≥ 0: `convN` with s = 0 to `([1], S 1 0)`, then `speedM` with
x = 0 to `([1, 1], S 1 (d/(d+1)))`.
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

theorem step_S_space_nonneg {c d : ℝ} (hd : 0 ≤ d) {L L' : Line} (h : Step c d L L') {a e : ℝ}
    (hk : L'.2 = .S a e) : 0 ≤ e := by
  cases h with
  | convMerge u rest a' s hs hsa hb =>
    injection hk with _ h2
    rw [← h2]
    exact mul_nonneg hd hs.le
  | convNew bl q a' s hq hs hsa hb =>
    injection hk with _ h2
    rw [← h2]
    exact mul_nonneg hd hs.le
  | speedMerge u rest a' e' x ha he hex hx hx1 hb =>
    injection hk with _ h2
    rw [← h2]
    exact he
  | speedNew bl q a' e' x hq ha he hex hx hx1 hb =>
    injection hk with _ h2
    rw [← h2]
    exact he
  | slow u rest k h1 h2 h3 h4 => cases hk

theorem path_S_space_nonneg {c d a₀ : ℝ} (hd : 0 ≤ d) {M : ℕ → Line} {n : ℕ}
    (hp : Path (Step c d) M n) (h0 : M 0 = ([], .T a₀)) :
    ∀ i ≤ n, ∀ a e : ℝ, (M i).2 = .S a e → 0 ≤ e := by
  intro i hi a e hk
  cases i with
  | zero => rw [h0] at hk; cases hk
  | succ j => exact step_S_space_nonneg hd (hp j (by omega)) hk

theorem step_S_space_nonnegO {ℓ : ℝ → ℝ → ℝ} {c d : ℝ} (hd : 0 ≤ d) {L L' : Line}
    (h : StepO ℓ c d L L') {a e : ℝ} (hk : L'.2 = .S a e) : 0 ≤ e := by
  cases h with
  | convMerge u rest a' s hs hsa hb =>
    injection hk with _ h2
    rw [← h2]
    exact mul_nonneg hd hs.le
  | convNew bl q a' s hq hs hsa hb =>
    injection hk with _ h2
    rw [← h2]
    exact mul_nonneg hd hs.le
  | speedMerge u rest a' e' x ha he hex hx hx1 hb =>
    injection hk with _ h2
    rw [← h2]
    exact he
  | speedNew bl q a' e' x hq ha he hex hx hx1 hb =>
    injection hk with _ h2
    rw [← h2]
    exact he
  | slow u rest k h1 h2 h3 h4 => cases hk

theorem path_S_space_nonnegO {ℓ : ℝ → ℝ → ℝ} {c d a₀ : ℝ} (hd : 0 ≤ d) {M : ℕ → Line} {n : ℕ}
    (hp : Path (StepO ℓ c d) M n) (h0 : M 0 = ([], .T a₀)) :
    ∀ i ≤ n, ∀ a e : ℝ, (M i).2 = .S a e → 0 ≤ e := by
  intro i hi a e hk
  cases i with
  | zero => rw [h0] at hk; cases hk
  | succ j => exact step_S_space_nonnegO hd (hp j (by omega)) hk

end HY

namespace HL

theorem cor78_base_reach (c d : ℝ) (hd : 0 ≤ d) :
    RStep c d ([], .T ((d + 1) / (d + 2))) ([1], .S 1 0) ∧
      RStep c d ([1], .S 1 0) ([1, 1], .S 1 (d / (d + 1))) := by
  have hd2 : 0 < d + 2 := by linarith
  have hA0 : 0 ≤ (d + 1) / (d + 2) := div_nonneg (by linarith) hd2.le
  have hA1 : (d + 1) / (d + 2) ≤ 1 := (div_le_one hd2).mpr (by linarith)
  refine ⟨?_, ?_⟩
  · refine RStep.convN [] ((d + 1) / (d + 2)) 0 1 1 0 le_rfl hA0 ?_ hA1 (by simp)
    simp only [pin, sub_zero]
    exact max_le zero_le_one hA1
  · refine RStep.speedM 1 [] 1 0 0 1 1 1 (d / (d + 1)) le_rfl (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_
    exact div_nonneg hd (by linarith)

end HL
end PastaMath.OneTapeThreshold
