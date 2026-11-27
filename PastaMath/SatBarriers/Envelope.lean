-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Cubic

namespace PastaMath.SatBarriers

theorem chunk_cost_lower {c x y M : ℝ} (hc : 1 ≤ c) (hyx : y ≤ x) :
    max (c * M) (x + (c - 1) * M) ≤ x - y + c * max y M := by
  have h1 : M ≤ max y M := le_max_right _ _
  have h2 : y ≤ max y M := le_max_left _ _
  apply max_le
  · nlinarith
  · nlinarith

theorem chunk_cost_attained {c x M : ℝ} (hM : 0 ≤ M) (hx : 0 ≤ x) :
    ∃ y, 0 ≤ y ∧ y ≤ x ∧ x - y + c * max y M = max (c * M) (x + (c - 1) * M) := by
  rcases le_total x M with h | h
  · refine ⟨x, hx, le_refl x, ?_⟩
    rw [max_eq_right h, sub_self, zero_add]
    rw [max_eq_left]
    nlinarith [h]
  · refine ⟨M, hM, h, ?_⟩
    rw [max_self]
    rcases le_total (c * M) (x + (c - 1) * M) with h' | h'
    · rw [max_eq_right h']; ring
    · have : x + (c - 1) * M = c * M := by nlinarith
      rw [max_eq_left h']; linarith

theorem step10_bound {c b d x d' : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) (hb : 0 ≤ b) (hxb : b ≤ x)
    (hd' : max (c * max b (d - x)) (x + (c - 1) * max b (d - x)) ≤ d') :
    (c - 1) * d ≤ d' ∧ c * b ≤ d' := by
  have hA := le_trans (le_max_left _ _) hd'
  have hB := le_trans (le_max_right _ _) hd'
  have m1 : b ≤ max b (d - x) := le_max_left _ _
  have m2 : d - x ≤ max b (d - x) := le_max_right _ _
  refine ⟨?_, by nlinarith⟩
  rcases le_total (2 * x) d with h | h
  · nlinarith
  · nlinarith

theorem first_step_redundant {c d x b : ℝ} (hc : 0 < c) (hx : x ≤ (c - 1) * d / c) :
    d ≤ c * max b (d - x) := by
  have : c * x ≤ (c - 1) * d := by rwa [le_div_iff₀ hc, mul_comm] at hx
  have h2 : d - x ≤ max b (d - x) := le_max_right _ _
  nlinarith

theorem btrivial_bound {c ν d x z u : ℝ} (hc1 : 1 < c) (hν : 0 < ν) (hνs : (c - 1) * ν ≤ 1)
    (hz : ν * (d - x) ≤ z)
    (hu : max (c * z) (x + (c - 1) * z) ≤ u) :
    c * ν * d / (1 + ν) ≤ u := by
  have hA := le_trans (le_max_left _ _) hu
  have hB := le_trans (le_max_right _ _) hu
  have hpos : 0 < 1 + ν := by linarith
  rw [div_le_iff₀ hpos]
  have hcz : c * (ν * (d - x)) ≤ c * z := mul_le_mul_of_nonneg_left hz (by linarith)
  have hcz' : (c - 1) * (ν * (d - x)) ≤ (c - 1) * z := mul_le_mul_of_nonneg_left hz (by linarith)
  rcases le_total (x * (1 + ν)) (ν * d) with h | h
  · have e1 : c * ν * (d - x) * (1 + ν) ≤ u * (1 + ν) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hpos.le
    have e2 : 0 ≤ c * ν * (ν * d - x * (1 + ν)) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith
  · have e1 : (x + (c - 1) * (ν * (d - x))) * (1 + ν) ≤ u * (1 + ν) :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    have e2 : 0 ≤ (1 - (c - 1) * ν) * (x * (1 + ν) - ν * d) := by
      apply mul_nonneg <;> linarith
    nlinarith

theorem btrivial_bound_big {c ν d x z u : ℝ} (hc1 : 1 < c) (hνs : 1 < (c - 1) * ν)
    (hxd : x ≤ d) (hz : ν * (d - x) ≤ z)
    (hu : max (c * z) (x + (c - 1) * z) ≤ u) :
    d ≤ u := by
  have hB := le_trans (le_max_right _ _) hu
  have hdx : 0 ≤ d - x := by linarith
  have : (d - x) ≤ (c - 1) * (ν * (d - x)) := by nlinarith
  nlinarith

theorem c_ge_two_removal {c a x : ℝ} (hc : 2 ≤ c) (hx : x ≤ a) :
    a ≤ max (c * (a - x)) (x + (c - 1) * (a - x)) := by
  apply le_trans _ (le_max_right _ _)
  nlinarith

theorem D_dominated {c μ ν : ℝ} (hc1 : 1 < c) (hc2 : c < 2) (hphi : 1 ≤ c * (c - 1))
    (hμ : 1 ≤ μ) (hν : 0 < ν) :
    1 ≤ c * (c - 1) * μ ∧ c * (c - 1) * μ ≤ c * μ ∧
      c * 1 * (c - 1) * ν / (1 + (c - 1) * ν) ≤ c * ν / (1 + ν) := by
  have hcm : 0 < c - 1 := by linarith
  have hcc : 0 ≤ c * (c - 1) := by positivity
  have a1 : c * (c - 1) * 1 ≤ c * (c - 1) * μ := mul_le_mul_of_nonneg_left hμ hcc
  have a2 : c * μ * (c - 1) ≤ c * μ * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine ⟨by linarith, by linarith, ?_⟩
  have h1 : 0 < 1 + (c - 1) * ν := by positivity
  have h2 : 0 < 1 + ν := by positivity
  rw [div_le_div_iff₀ h1 h2]
  have hcν : 0 ≤ c * ν := by positivity
  have a3 : c * ν * ((c - 1) * (1 + ν)) ≤ c * ν * (1 + (c - 1) * ν) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hcν
  have e : c * 1 * (c - 1) * ν * (1 + ν) = c * ν * ((c - 1) * (1 + ν)) := by ring
  rw [e]; exact a3

end PastaMath.SatBarriers
