-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.PairsExt

namespace PastaMath.SatBarriers

noncomputable def gam (c β : ℝ) : ℝ := c - β * (c - 1)

theorem step10_bound_beta {c β b d x d' : ℝ} (hc1 : 1 < c) (hβ0 : 0 ≤ β)
    (hβ1 : β * (c - 1) ≤ 1) (hd : 0 ≤ d)
    (hβc : (c - 1) * (1 + gam c β) ≤ c)
    (hd' : max (c * max b (d - x)) (x + β * (c - 1) * max b (d - x)) ≤ d') :
    (c - 1) * d ≤ d' ∧ c * b ≤ d' := by
  unfold gam at hβc
  have hA := le_trans (le_max_left _ _) hd'
  have hB := le_trans (le_max_right _ _) hd'
  have m1 : b ≤ max b (d - x) := le_max_left _ _
  have m2 : d - x ≤ max b (d - x) := le_max_right _ _
  have hc0 : 0 < c := by linarith
  refine ⟨?_, by nlinarith⟩
  have hβc0 : 0 ≤ β * (c - 1) := mul_nonneg hβ0 (by linarith)
  have e1 : c * (d - x) ≤ d' := by nlinarith
  have e2 : x + β * (c - 1) * (d - x) ≤ d' := by
    have := mul_le_mul_of_nonneg_left m2 hβc0
    linarith
  have comb : c * d ≤ (1 + (c - β * (c - 1))) * d' := by
    have f1 := mul_le_mul_of_nonneg_left e1 (by linarith : (0 : ℝ) ≤ 1 - β * (c - 1))
    have f2 := mul_le_mul_of_nonneg_left e2 hc0.le
    nlinarith
  have hpos : 0 < 1 + (c - β * (c - 1)) := by nlinarith
  have := mul_le_mul_of_nonneg_right hβc hd
  nlinarith

theorem btrivial_bound_beta {c β ν d x z u : ℝ} (hc1 : 1 < c) (hν : 0 < ν) (hβ0 : 0 ≤ β)
    (hβν : β * (c - 1) * ν ≤ 1)
    (hz : ν * (d - x) ≤ z) (hu : max (c * z) (x + β * (c - 1) * z) ≤ u) :
    c * ν * d / (1 + gam c β * ν) ≤ u := by
  unfold gam
  have hA := le_trans (le_max_left _ _) hu
  have hB := le_trans (le_max_right _ _) hu
  have hc0 : 0 < c := by linarith
  have hβc0 : 0 ≤ β * (c - 1) := mul_nonneg hβ0 (by linarith)
  have e1 : c * (ν * (d - x)) ≤ u := le_trans (mul_le_mul_of_nonneg_left hz hc0.le) hA
  have e2 : x + β * (c - 1) * (ν * (d - x)) ≤ u := by
    have := mul_le_mul_of_nonneg_left hz hβc0
    linarith
  have hD : 0 < 1 + (c - β * (c - 1)) * ν := by nlinarith
  rw [div_le_iff₀ hD]
  have f1 := mul_le_mul_of_nonneg_left e1 (by linarith : (0 : ℝ) ≤ 1 - β * (c - 1) * ν)
  have f2 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ c * ν)
  nlinarith

theorem btrivial_bound_beta_big {c β ν d x z u : ℝ} (hc1 : 1 < c) (hβ0 : 0 ≤ β)
    (hβν : 1 < β * (c - 1) * ν) (hxd : x ≤ d) (hz : ν * (d - x) ≤ z)
    (hu : max (c * z) (x + β * (c - 1) * z) ≤ u) :
    d ≤ u := by
  have hB := le_trans (le_max_right _ _) hu
  have hβc0 : 0 ≤ β * (c - 1) := mul_nonneg hβ0 (by linarith)
  have hdx : 0 ≤ d - x := by linarith
  have e : β * (c - 1) * (ν * (d - x)) ≤ β * (c - 1) * z := mul_le_mul_of_nonneg_left hz hβc0
  have : d - x ≤ β * (c - 1) * ν * (d - x) := by nlinarith
  nlinarith

theorem inv_dbeta {c β : ℝ} (hc : r7 ≤ c) (hγ : 0 < gam c β)
    (hβ2 : c * (2 - c) ≤ β * (c - 1)) (hγτ : gam c β * tau0 c ≤ c - 1)
    {μ ν : ℝ} (ih : Inv c μ ν) :
    Inv c (c * μ) (c * ν / (1 + gam c β * ν)) := by
  have h1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  have hc0 : 0 < c := by linarith
  obtain ⟨i1, i2, i3, i4⟩ := ih
  have hD : 0 < 1 + gam c β * ν := by positivity
  refine ⟨by nlinarith, by positivity, ?_, ?_⟩
  · have key : tau0 c * ν ≤ (c ^ 2 * ν - 1 - gam c β * ν) * μ := by
      have hg : c ^ 2 - c - gam c β ≥ 0 := by unfold gam; nlinarith
      have : 0 ≤ (c ^ 2 - c - gam c β) * ν * μ := by
        apply mul_nonneg (mul_nonneg hg i2.le) (by linarith)
      nlinarith
    have e1 : tau0 c * (c * ν / (1 + gam c β * ν)) = (tau0 c * ν * c) / (1 + gam c β * ν) := by
      ring
    have e2 : (c * (c * ν / (1 + gam c β * ν)) - 1) * (c * μ)
        = ((c ^ 2 * ν - 1 - gam c β * ν) * μ * c) / (1 + gam c β * ν) := by
      field_simp
      ring
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ hD.le
    nlinarith
  · rw [lt_div_iff₀ hD]
    have := mul_le_mul_of_nonneg_right hγτ i2.le
    nlinarith

inductive ABEFD (c β : ℝ) : ℝ → ℝ → Prop
  | base : ABEFD c β 1 (c - 1)
  | comp {μ₁ ν₁ μ₂ ν₂ : ℝ} : ABEFD c β μ₁ ν₁ → ABEFD c β μ₂ ν₂ → μ₁ ≤ c * ν₁ * μ₂ →
      ABEFD c β (c * ν₁ * μ₂) (c * μ₁ * ν₁ * ν₂ / (μ₁ + ν₁ * ν₂))
  | weaken {μ ν μ' ν' : ℝ} : ABEFD c β μ ν → μ ≤ μ' → ν ≤ ν' → ν' ≤ 1 → ABEFD c β μ' ν'
  | big {μ ν : ℝ} : 1 ≤ μ → 1 ≤ ν → ABEFD c β μ ν
  | dbeta {μ ν : ℝ} : ABEFD c β μ ν → ABEFD c β (c * μ) (c * ν / (1 + gam c β * ν))

theorem ABEF.toABEFD {c β μ ν : ℝ} (h : ABEF c μ ν) : ABEFD c β μ ν := by
  induction h with
  | base => exact ABEFD.base
  | comp _ _ hside ih1 ih2 => exact ABEFD.comp ih1 ih2 hside
  | weaken _ hμ hν h1 ih => exact ABEFD.weaken ih hμ hν h1
  | big hμ hν => exact ABEFD.big hμ hν

theorem abefd_invariant {c β : ℝ} (hc : r7 ≤ c) (hc2 : c < 2) (hγ : 0 < gam c β)
    (hβ2 : c * (2 - c) ≤ β * (c - 1)) (hγτ : gam c β * tau0 c ≤ c - 1)
    {μ ν : ℝ} (h : ABEFD c β μ ν) : Inv c μ ν := by
  induction h with
  | base => exact inv_base hc hc2
  | comp _ _ hside ih1 ih2 => exact inv_comp hc ih1 ih2 hside
  | weaken _ hμ hν _ ih => exact inv_weaken hc ih hμ hν
  | big hμ hν => exact inv_big hc hc2 hμ hν
  | dbeta _ ih => exact inv_dbeta hc hγ hβ2 hγτ ih

theorem abefd_no_small_pair {c β : ℝ} (hc : r7 ≤ c) (hc2 : c < 2) (hγ : 0 < gam c β)
    (hβ2 : c * (2 - c) ≤ β * (c - 1)) (hγτ : gam c β * tau0 c ≤ c - 1)
    {μ ν : ℝ} (h : ABEFD c β μ ν) : 1 / c < ν :=
  lt_of_le_of_lt (tau0_ge_inv hc) (abefd_invariant hc hc2 hγ hβ2 hγτ h).2.2.2

theorem tau0_r7 : tau0 r7 = 1 / r7 := by
  have h1 := one_lt_r7
  have hc := cub_r7
  unfold cub at hc
  unfold tau0
  have hr0 : r7 ≠ 0 := by linarith
  have hr1 : r7 - 1 ≠ 0 := by linarith
  field_simp
  nlinarith

theorem beta_star_conditions {β : ℝ} (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hβ1 : β ≤ 1) :
    (r7 - 1) * (1 + gam r7 β) ≤ r7 ∧ r7 * (2 - r7) ≤ β * (r7 - 1) ∧
      gam r7 β * tau0 r7 ≤ r7 - 1 ∧ 0 < gam r7 β ∧ β * (r7 - 1) ≤ 1 ∧ 0 ≤ β := by
  have h1 := one_lt_r7
  have h2 := r7_lt_two
  have hc := cub_r7
  unfold cub at hc
  have hpos : 0 < r7 * (r7 - 1) := by nlinarith
  have hprod : 1 ≤ β * (r7 * (r7 - 1)) := by
    rw [div_le_iff₀ hpos] at hβ
    linarith
  have hβ0 : 0 ≤ β := by
    have : 0 < 1 / (r7 * (r7 - 1)) := by positivity
    linarith
  have hii : r7 * (2 - r7) ≤ β * (r7 - 1) := by
    have hsq : r7 * (2 - r7) * r7 ≤ 1 := by nlinarith
    have : r7 * (2 - r7) * r7 ≤ β * (r7 - 1) * r7 := by nlinarith
    nlinarith
  unfold gam
  refine ⟨?_, hii, ?_, by nlinarith, by nlinarith, hβ0⟩
  · have hm : (r7 - 1) * (r7 * (r7 ^ 2 - r7 - 1)) ≤ (r7 - 1) * (r7 * (β * (r7 - 1) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    nlinarith
  · rw [tau0_r7]
    have : (r7 - β * (r7 - 1)) ≤ (r7 - 1) * r7 := by nlinarith
    rw [show (r7 - β * (r7 - 1)) * (1 / r7) = (r7 - β * (r7 - 1)) / r7 by ring,
      div_le_iff₀ (by linarith)]
    linarith

theorem pair_calculus_beta {β : ℝ} (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hβ1 : β ≤ 1)
    {μ ν : ℝ} (h : ABEFD r7 β μ ν) : 1 / r7 < ν := by
  obtain ⟨_, hii, hiii, hγ, _, _⟩ := beta_star_conditions hβ hβ1
  exact abefd_no_small_pair le_rfl r7_lt_two hγ hii hiii h

theorem one_step_base_at_beta_star :
    (r7 - 1) * (1 + gam r7 (1 / (r7 * (r7 - 1)))) = r7 := by
  have h1 := one_lt_r7
  have hc := cub_r7
  unfold cub at hc
  unfold gam
  have hr0 : r7 ≠ 0 := by linarith
  have hr1 : r7 - 1 ≠ 0 := by linarith
  field_simp
  nlinarith

theorem one_step_tau_below_beta_star {β : ℝ} (hβ : β < 1 / (r7 * (r7 - 1))) :
    tau r7 1 (r7 / (1 + gam r7 β)) < 1 / r7 := by
  have h1 := one_lt_r7
  have h2 := r7_lt_two
  have hc := cub_r7
  unfold cub at hc
  have hpos : 0 < r7 * (r7 - 1) := by nlinarith
  have hprod : β * (r7 * (r7 - 1)) < 1 := by
    rw [lt_div_iff₀ hpos] at hβ
    linarith
  unfold tau gam
  have hr0 : 0 < r7 := by linarith
  have hD : 0 < 1 + (r7 - β * (r7 - 1)) := by nlinarith
  rw [one_div_div, mul_one, sub_lt_iff_lt_add]
  have e : 1 / r7 + (1 + (r7 - β * (r7 - 1))) / r7 = (2 + r7 - β * (r7 - 1)) / r7 := by
    field_simp; ring
  rw [e, lt_div_iff₀ hr0]
  nlinarith

end PastaMath.SatBarriers
