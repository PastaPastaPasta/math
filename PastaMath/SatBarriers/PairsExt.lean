-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Pairs

namespace PastaMath.SatBarriers

inductive ABEF (c : ℝ) : ℝ → ℝ → Prop
  | base : ABEF c 1 (c - 1)
  | comp {μ₁ ν₁ μ₂ ν₂ : ℝ} : ABEF c μ₁ ν₁ → ABEF c μ₂ ν₂ → μ₁ ≤ c * ν₁ * μ₂ →
      ABEF c (c * ν₁ * μ₂) (c * μ₁ * ν₁ * ν₂ / (μ₁ + ν₁ * ν₂))
  | weaken {μ ν μ' ν' : ℝ} : ABEF c μ ν → μ ≤ μ' → ν ≤ ν' → ν' ≤ 1 → ABEF c μ' ν'
  | big {μ ν : ℝ} : 1 ≤ μ → 1 ≤ ν → ABEF c μ ν

theorem ABE.toABEF {c μ ν : ℝ} (h : ABE c μ ν) : ABEF c μ ν := by
  induction h with
  | base => exact ABEF.base
  | weaken _ hμ hν h1 ih => exact ABEF.weaken ih hμ hν h1
  | comp _ _ hside ih1 ih2 => exact ABEF.comp ih1 ih2 hside

theorem inv_big {c : ℝ} (hc : r7 ≤ c) (hc2 : c < 2) {μ ν : ℝ} (hμ : 1 ≤ μ) (hν : 1 ≤ ν) :
    Inv c μ ν := by
  have h1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  have hcm : 0 < c - 1 := by linarith
  have hlt : tau0 c < 1 := by
    unfold tau0
    have : 1 < 1 / (c - 1) := by rw [lt_div_iff₀ hcm]; linarith
    linarith
  have hgap : 1 ≤ (c - tau0 c) * ν := by
    unfold tau0
    have : 1 < 1 / (c - 1) := by rw [lt_div_iff₀ hcm]; linarith
    nlinarith
  refine ⟨hμ, by linarith, ?_, by linarith⟩
  have hpos : 0 ≤ c * ν - 1 := by nlinarith
  have : (c * ν - 1) * 1 ≤ (c * ν - 1) * μ := mul_le_mul_of_nonneg_left hμ hpos
  nlinarith

theorem abef_invariant {c : ℝ} (hc : r7 ≤ c) (hc2 : c < 2) {μ ν : ℝ} (h : ABEF c μ ν) :
    Inv c μ ν := by
  induction h with
  | base => exact inv_base hc hc2
  | weaken _ hμ hν _ ih => exact inv_weaken hc ih hμ hν
  | comp _ _ hside ih1 ih2 => exact inv_comp hc ih1 ih2 hside
  | big hμ hν => exact inv_big hc hc2 hμ hν

theorem abef_nu_ge_one {c : ℝ} (hc : 2 ≤ c) {μ ν : ℝ} (h : ABEF c μ ν) : 1 ≤ μ ∧ 1 ≤ ν := by
  induction h with
  | base => exact ⟨le_refl 1, by linarith⟩
  | weaken _ hμ hν _ ih => exact ⟨le_trans ih.1 hμ, le_trans ih.2 hν⟩
  | big hμ hν => exact ⟨hμ, hν⟩
  | @comp μ₁ ν₁ μ₂ ν₂ _ _ hside ih1 ih2 =>
    obtain ⟨a1, a2⟩ := ih1
    obtain ⟨b1, b2⟩ := ih2
    refine ⟨le_trans a1 hside, ?_⟩
    have hden : 0 < μ₁ + ν₁ * ν₂ := by positivity
    rw [le_div_iff₀ hden, one_mul]
    have h12 : 1 ≤ ν₁ * ν₂ := by nlinarith
    have : 2 * (μ₁ * (ν₁ * ν₂)) ≤ c * (μ₁ * (ν₁ * ν₂)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    nlinarith

theorem abef_no_small_pair {c : ℝ} (hc : r7 ≤ c) {μ ν : ℝ} (h : ABEF c μ ν) : 1 / c < ν := by
  have h1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  rcases lt_or_ge c 2 with h2 | h2
  · exact lt_of_le_of_lt (tau0_ge_inv hc) (abef_invariant hc h2 h).2.2.2
  · have := (abef_nu_ge_one h2 h).2
    have : 1 / c < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith

theorem pairF_threshold {c : ℝ} (hc : 1 < c) : (∃ μ ν, ABEF c μ ν ∧ ν < 1 / c) ↔ c < r7 := by
  constructor
  · rintro ⟨μ, ν, h, hν⟩
    by_contra hh
    push Not at hh
    linarith [abef_no_small_pair hh h]
  · intro hr
    obtain ⟨μ, ν, h, hν⟩ := exists_small_pair hc hr
    exact ⟨μ, ν, h.toABEF, hν⟩

end PastaMath.SatBarriers
