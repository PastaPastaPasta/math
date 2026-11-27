-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PastaMath.SatBarriers

open Real

noncomputable def r7 : ℝ := 2 * Real.cos (π / 7)

def cub (x : ℝ) : ℝ := x ^ 3 - x ^ 2 - 2 * x + 1

theorem cos_pi_div_seven_pos : 0 < Real.cos (π / 7) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

theorem cub_r7 : cub r7 = 0 := by
  have h4 : Real.cos (4 * (π / 7)) = -Real.cos (3 * (π / 7)) := by
    rw [show 4 * (π / 7) = π - 3 * (π / 7) by ring, Real.cos_pi_sub]
  have h2 : Real.cos (4 * (π / 7)) = 2 * (2 * Real.cos (π / 7) ^ 2 - 1) ^ 2 - 1 := by
    rw [show 4 * (π / 7) = 2 * (2 * (π / 7)) by ring, Real.cos_two_mul, Real.cos_two_mul]
  rw [Real.cos_three_mul] at h4
  have hy := cos_pi_div_seven_pos
  set y := Real.cos (π / 7)
  have h : 2 * (2 * y ^ 2 - 1) ^ 2 - 1 = -(4 * y ^ 3 - 3 * y) := by rw [← h2, h4]
  have key : (2 * y + 2) * cub (2 * y) = 0 := by
    unfold cub; linear_combination 2 * h
  have hne : (2 * y + 2) ≠ 0 := by positivity
  unfold r7
  exact (mul_eq_zero.mp key).resolve_left hne

theorem one_lt_r7 : 1 < r7 := by
  have h : Real.cos (π / 3) < Real.cos (π / 7) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · positivity
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  rw [Real.cos_pi_div_three] at h
  unfold r7; linarith

theorem r7_lt_two : r7 < 2 := by
  have h : Real.cos (π / 7) < Real.cos 0 := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · exact le_refl 0
    · linarith [Real.pi_pos]
    · positivity
  rw [Real.cos_zero] at h
  unfold r7; linarith

theorem two_lt_r7_sq : 2 < r7 ^ 2 := by
  have h : Real.cos (π / 4) < Real.cos (π / 7) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · positivity
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  rw [Real.cos_pi_div_four] at h
  have hs : (0 : ℝ) < √2 / 2 := by positivity
  have hsq : (√2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have : (√2 / 2) ^ 2 < Real.cos (π / 7) ^ 2 := by
    apply pow_lt_pow_left₀ h hs.le (by norm_num)
  unfold r7
  nlinarith

theorem cub_sub_r7 (c : ℝ) :
    cub c = (c - r7) * ((c ^ 2 - c) + c * r7 + (r7 ^ 2 - r7 - 2)) := by
  have h := cub_r7
  unfold cub at *
  linear_combination h

theorem cub_factor_pos {c : ℝ} (hc : 1 ≤ c) :
    0 < (c ^ 2 - c) + c * r7 + (r7 ^ 2 - r7 - 2) := by
  have h1 := one_lt_r7
  have h2 := two_lt_r7_sq
  nlinarith

theorem cub_neg_iff {c : ℝ} (hc : 1 ≤ c) : cub c < 0 ↔ c < r7 := by
  rw [cub_sub_r7]
  have hp := cub_factor_pos hc
  constructor
  · intro h
    by_contra hh
    push Not at hh
    have : 0 ≤ (c - r7) * ((c ^ 2 - c) + c * r7 + (r7 ^ 2 - r7 - 2)) :=
      mul_nonneg (by linarith) hp.le
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos (by linarith) hp

theorem cub_nonneg_iff {c : ℝ} (hc : 1 ≤ c) : 0 ≤ cub c ↔ r7 ≤ c := by
  have := cub_neg_iff hc
  constructor
  · intro h; by_contra hh; push Not at hh; linarith [this.mpr hh]
  · intro h; by_contra hh; push Not at hh; linarith [this.mp hh]

theorem cub_eq_zero_iff {c : ℝ} (hc : 1 ≤ c) : cub c = 0 ↔ c = r7 := by
  rw [cub_sub_r7]
  have hp := cub_factor_pos hc
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · linarith
  · intro h; rw [h]; ring

noncomputable def tau (c μ ν : ℝ) : ℝ := (c - 1 / ν) * μ

theorem tau_base_lt_iff {c : ℝ} (hc : 1 < c) : tau c 1 (c - 1) < 1 / c ↔ cub c < 0 := by
  unfold tau cub
  have h1 : 0 < c - 1 := by linarith
  have h0 : 0 < c := by linarith
  have e : (c - 1 / (c - 1)) * 1 - 1 / c = (c ^ 3 - c ^ 2 - 2 * c + 1) / (c * (c - 1)) := by
    field_simp; ring
  constructor
  · intro h
    have : (c ^ 3 - c ^ 2 - 2 * c + 1) / (c * (c - 1)) < 0 := by linarith
    have hd : 0 < c * (c - 1) := by positivity
    by_contra hh; push Not at hh
    have : 0 ≤ (c ^ 3 - c ^ 2 - 2 * c + 1) / (c * (c - 1)) := div_nonneg hh hd.le
    linarith
  · intro h
    have hd : 0 < c * (c - 1) := by positivity
    have : (c ^ 3 - c ^ 2 - 2 * c + 1) / (c * (c - 1)) < 0 := div_neg_of_neg_of_pos h hd
    linarith

theorem tau_base_lt_iff_r7 {c : ℝ} (hc : 1 < c) : tau c 1 (c - 1) < 1 / c ↔ c < r7 :=
  (tau_base_lt_iff hc).trans (cub_neg_iff hc.le)

noncomputable def condSpeed (c : ℝ) : ℕ → ℝ
  | 0 => 2
  | k + 1 => 1 + condSpeed c k / c

theorem condSpeed_closed {c : ℝ} (hc : 1 < c) (k : ℕ) :
    condSpeed c k = c / (c - 1) - (c / (c - 1) - 2) * (1 / c) ^ k := by
  have h1 : (c - 1) ≠ 0 := by linarith
  have h0 : c ≠ 0 := by linarith
  induction k with
  | zero => simp [condSpeed]
  | succ k ih =>
    rw [condSpeed, ih, pow_succ]
    field_simp
    ring

theorem condSpeed_tendsto {c : ℝ} (hc : 1 < c) (hc2 : c < 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, c / (c - 1) - ε < condSpeed c k ∧ condSpeed c k < c / (c - 1) := by
  have h1 : 0 < c - 1 := by linarith
  have hA : 0 < c / (c - 1) - 2 := by
    rw [div_sub' (by linarith)]; apply div_pos <;> linarith
  have hq0 : 0 < 1 / c := by positivity
  have hq1 : 1 / c < 1 := by rw [div_lt_one (by linarith)]; exact hc
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hA) hq1
  refine ⟨k, ?_, ?_⟩
  · rw [condSpeed_closed hc]
    have : (c / (c - 1) - 2) * (1 / c) ^ k < ε := by
      rw [lt_div_iff₀ hA] at hk; linarith
    linarith
  · rw [condSpeed_closed hc]
    have : 0 < (c / (c - 1) - 2) * (1 / c) ^ k := mul_pos hA (pow_pos hq0 k)
    linarith

theorem w08_arith {c : ℝ} (hc : 1 < c) (hc2 : c < 2) (hphi : 1 < c * (c - 1)) (hcub : cub c < 0) :
    ∃ d : ℝ, ∃ k : ℕ, c ≤ d ∧ d ≤ c ^ 2 ∧ d < c / (c - 1) ∧
      c ^ 2 * (c ^ 2 / d) ^ k < d + ∑ i ∈ Finset.range k, (c ^ 2 / d) ^ (i + 1) := by
  have h1 : 0 < c - 1 := by linarith
  have h0 : 0 < c := by linarith
  have hlow : c ^ 2 - 1 < c / (c - 1) := by
    rw [lt_div_iff₀ h1]; unfold cub at hcub; nlinarith
  set d := (c ^ 2 - 1 + c / (c - 1)) / 2 with hd
  have hd1 : c ^ 2 - 1 < d := by rw [hd]; linarith
  have hd2 : d < c / (c - 1) := by rw [hd]; linarith
  have hcd : c ≤ d := by nlinarith
  have hdpos : 0 < d := by linarith
  have hupper : c / (c - 1) < c ^ 2 := by
    rw [div_lt_iff₀ h1]; nlinarith
  have hdc2 : d ≤ c ^ 2 := by linarith
  set q := c ^ 2 / d with hq
  have hq1 : 1 < q := by rw [hq, lt_div_iff₀ hdpos]; linarith
  have hqd : q * d = c ^ 2 := by rw [hq]; field_simp
  have hA : 0 < q * (d + 1 - c ^ 2) := by
    apply mul_pos (by linarith); linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((q + d) / (q * (d + 1 - c ^ 2))) hq1
  refine ⟨d, k, hcd, hdc2, hd2, ?_⟩
  have hS : (∑ i ∈ Finset.range k, q ^ (i + 1)) * (q - 1) = q * (q ^ k - 1) := by
    rw [show (∑ i ∈ Finset.range k, q ^ (i + 1)) = q * ∑ i ∈ Finset.range k, q ^ i by
      rw [Finset.mul_sum]; congr 1; ext i; ring]
    rw [mul_assoc, geom_sum_mul]
  rw [div_lt_iff₀ hA] at hk
  set P := q ^ k with hP
  set S := ∑ i ∈ Finset.range k, q ^ (i + 1) with hSdef
  have hq1' : 0 < q - 1 := by linarith
  have hc2pos : 0 < c ^ 2 := by positivity
  have id : (q - 1) * d + q * P - q - (q - 1) * (c ^ 2 * P)
      = (P * (q * (d + 1 - c ^ 2)) - (q + d)) + c ^ 2 := by
    linear_combination (1 - P) * hqd
  have hexp : (q - 1) * (d + S) = (q - 1) * d + q * P - q := by
    linear_combination hS
  have h2 : (q - 1) * (c ^ 2 * P) < (q - 1) * (d + S) := by
    rw [hexp]; linarith
  exact lt_of_mul_lt_mul_left h2 hq1'.le

end PastaMath.SatBarriers
