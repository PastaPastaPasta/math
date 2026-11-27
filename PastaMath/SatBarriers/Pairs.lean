-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Cubic

namespace PastaMath.SatBarriers

inductive ABE (c : ℝ) : ℝ → ℝ → Prop
  | base : ABE c 1 (c - 1)
  | comp {μ₁ ν₁ μ₂ ν₂ : ℝ} : ABE c μ₁ ν₁ → ABE c μ₂ ν₂ → μ₁ ≤ c * ν₁ * μ₂ →
      ABE c (c * ν₁ * μ₂) (c * μ₁ * ν₁ * ν₂ / (μ₁ + ν₁ * ν₂))
  | weaken {μ ν μ' ν' : ℝ} : ABE c μ ν → μ ≤ μ' → ν ≤ ν' → ν' ≤ 1 → ABE c μ' ν'

noncomputable def tau0 (c : ℝ) : ℝ := c - 1 / (c - 1)

theorem tau0_ge_inv {c : ℝ} (hc : r7 ≤ c) : 1 / c ≤ tau0 c := by
  have h1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  have h := tau_base_lt_iff_r7 h1
  unfold tau at h
  unfold tau0
  by_contra hh
  push Not at hh
  have : (c - 1 / (c - 1)) * 1 < 1 / c := by linarith
  linarith [h.mp this]

def Inv (c μ ν : ℝ) : Prop := 1 ≤ μ ∧ 0 < ν ∧ tau0 c * ν ≤ (c * ν - 1) * μ ∧ tau0 c < ν

theorem inv_base {c : ℝ} (hc : r7 ≤ c) (hc2 : c < 2) : Inv c 1 (c - 1) := by
  have h1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  have hc0 : 0 < c := by linarith
  have ht := tau0_ge_inv hc
  have hinv : 0 < 1 / c := by positivity
  have ht0 : 0 < tau0 c := lt_of_lt_of_le hinv ht
  have hct : 1 ≤ c * tau0 c := by
    have := mul_le_mul_of_nonneg_left ht hc0.le
    rwa [mul_one_div_cancel hc0.ne'] at this
  have hcm : 0 < c - 1 := by linarith
  refine ⟨le_refl 1, hcm, ?_, ?_⟩
  · unfold tau0
    have e : (c - 1 / (c - 1)) * (c - 1) = c * (c - 1) - 1 := by
      field_simp
    rw [e]; linarith
  · unfold tau0
    have : 1 < 1 / (c - 1) := by
      rw [lt_div_iff₀ hcm]; linarith
    linarith

theorem inv_weaken {c : ℝ} (hc : r7 ≤ c) {μ0 ν0 μ' ν' : ℝ} (ih : Inv c μ0 ν0)
    (hμ : μ0 ≤ μ') (hν : ν0 ≤ ν') : Inv c μ' ν' := by
  have h1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  have hc0 : 0 < c := by linarith
  have ht := tau0_ge_inv hc
  have hinv : 0 < 1 / c := by positivity
  have ht0 : 0 < tau0 c := lt_of_lt_of_le hinv ht
  have hct : 1 ≤ c * tau0 c := by
    have := mul_le_mul_of_nonneg_left ht hc0.le
    rwa [mul_one_div_cancel hc0.ne'] at this
  obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
  have hν' : 0 < ν' := lt_of_lt_of_le ih2 hν
  refine ⟨le_trans ih1 hμ, hν', ?_, lt_of_lt_of_le ih4 hν⟩
  have hcν : 1 < c * ν0 := by
    have := mul_lt_mul_of_pos_left ih4 hc0
    linarith
  have hcν' : 1 < c * ν' := by
    have := mul_le_mul_of_nonneg_left hν hc0.le
    linarith
  have a : tau0 c * ν0 * ν' ≤ (c * ν0 - 1) * μ0 * ν' :=
    mul_le_mul_of_nonneg_right ih3 hν'.le
  have b : (c * ν0 - 1) * ν' ≤ (c * ν' - 1) * ν0 := by nlinarith
  have b' : (c * ν0 - 1) * ν' * μ0 ≤ (c * ν' - 1) * ν0 * μ0 :=
    mul_le_mul_of_nonneg_right b (by linarith)
  have step1 : tau0 c * ν' * ν0 ≤ (c * ν' - 1) * μ0 * ν0 := by nlinarith
  have step2 : tau0 c * ν' ≤ (c * ν' - 1) * μ0 := le_of_mul_le_mul_right step1 ih2
  have step3 : (c * ν' - 1) * μ0 ≤ (c * ν' - 1) * μ' :=
    mul_le_mul_of_nonneg_left hμ (by linarith)
  linarith

theorem inv_comp {c : ℝ} (hc : r7 ≤ c) {μ₁ ν₁ μ₂ ν₂ : ℝ} (ih1 : Inv c μ₁ ν₁) (ih2 : Inv c μ₂ ν₂)
    (hside : μ₁ ≤ c * ν₁ * μ₂) :
    Inv c (c * ν₁ * μ₂) (c * μ₁ * ν₁ * ν₂ / (μ₁ + ν₁ * ν₂)) := by
  have h1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  have hc0 : 0 < c := by linarith
  have ht := tau0_ge_inv hc
  have hinv : 0 < 1 / c := by positivity
  have ht0 : 0 < tau0 c := lt_of_lt_of_le hinv ht
  have hct : 1 ≤ c * tau0 c := by
    have := mul_le_mul_of_nonneg_left ht hc0.le
    rwa [mul_one_div_cancel hc0.ne'] at this
  obtain ⟨a1, a2, a3, a4⟩ := ih1
  obtain ⟨b1, b2, b3, b4⟩ := ih2
  have hcν1 : 1 < c * ν₁ := by
    have := mul_lt_mul_of_pos_left a4 hc0
    linarith
  have hμ1 : 0 < μ₁ := by linarith
  have hμ2 : 0 < μ₂ := by linarith
  have hden : 0 < μ₁ + ν₁ * ν₂ := by positivity
  have hμ : 1 ≤ c * ν₁ * μ₂ := le_trans a1 hside
  have hνpos : 0 < c * μ₁ * ν₁ * ν₂ / (μ₁ + ν₁ * ν₂) := by
    apply div_pos _ hden
    positivity
  refine ⟨hμ, hνpos, ?_, ?_⟩
  · have hc0' : c ≠ 0 := hc0.ne'
    have hμ1' : μ₁ ≠ 0 := hμ1.ne'
    have hν1' : ν₁ ≠ 0 := a2.ne'
    have hν2' : ν₂ ≠ 0 := b2.ne'
    have hden' : μ₁ + ν₁ * ν₂ ≠ 0 := hden.ne'
    set ν := c * μ₁ * ν₁ * ν₂ / (μ₁ + ν₁ * ν₂) with hνdef
    have e2 : (c * ν - 1) * (c * ν₁ * μ₂) / ν
        = c ^ 2 * ν₁ * μ₂ - μ₂ / ν₂ - ν₁ * μ₂ / μ₁ := by
      rw [hνdef]; field_simp; ring
    have hτ2 : tau0 c ≤ c * μ₂ - μ₂ / ν₂ := by
      have e : c * μ₂ - μ₂ / ν₂ = (c * μ₂ * ν₂ - μ₂) / ν₂ := by field_simp
      rw [e, le_div_iff₀ b2]
      nlinarith
    have hτ1 : tau0 c ≤ c * μ₁ - μ₁ / ν₁ := by
      have e : c * μ₁ - μ₁ / ν₁ = (c * μ₁ * ν₁ - μ₁) / ν₁ := by field_simp
      rw [e, le_div_iff₀ a2]
      nlinarith
    have hτ1' : 1 ≤ c * (c * μ₁ - μ₁ / ν₁) := by
      have := mul_le_mul_of_nonneg_left hτ1 hc0.le
      linarith
    have hdiff : c * μ₂ - μ₂ / ν₂ ≤ c ^ 2 * ν₁ * μ₂ - μ₂ / ν₂ - ν₁ * μ₂ / μ₁ := by
      have e3 : c ^ 2 * ν₁ * μ₂ - μ₂ / ν₂ - ν₁ * μ₂ / μ₁ - (c * μ₂ - μ₂ / ν₂)
          = (ν₁ * μ₂ / μ₁) * (c * (c * μ₁ - μ₁ / ν₁) - 1) := by
        field_simp; ring
      have : 0 ≤ (ν₁ * μ₂ / μ₁) * (c * (c * μ₁ - μ₁ / ν₁) - 1) := by
        apply mul_nonneg
        · positivity
        · linarith
      linarith
    have hfin : tau0 c ≤ (c * ν - 1) * (c * ν₁ * μ₂) / ν := by
      rw [e2]; linarith
    rw [le_div_iff₀ hνpos] at hfin
    linarith
  · rw [lt_div_iff₀ hden]
    have h3 : tau0 c * ν₁ * ν₂ ≤ (c * ν₁ - 1) * μ₁ * ν₂ :=
      mul_le_mul_of_nonneg_right a3 b2.le
    have h4 : μ₁ * tau0 c < μ₁ * ν₂ := mul_lt_mul_of_pos_left b4 hμ1
    nlinarith


theorem abe_invariant {c : ℝ} (hc : r7 ≤ c) (hc2 : c < 2) {μ ν : ℝ} (h : ABE c μ ν) :
    Inv c μ ν := by
  induction h with
  | base => exact inv_base hc hc2
  | weaken _ hμ hν _ ih => exact inv_weaken hc ih hμ hν
  | comp _ _ hside ih1 ih2 => exact inv_comp hc ih1 ih2 hside

theorem abe_nu_ge_one {c : ℝ} (hc : 2 ≤ c) {μ ν : ℝ} (h : ABE c μ ν) : 1 ≤ μ ∧ 1 ≤ ν := by
  induction h with
  | base => exact ⟨le_refl 1, by linarith⟩
  | @weaken μ0 ν0 μ' ν' _ hμ hν _ ih => exact ⟨le_trans ih.1 hμ, le_trans ih.2 hν⟩
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

theorem no_small_pair {c : ℝ} (hc : r7 ≤ c) {μ ν : ℝ} (h : ABE c μ ν) : 1 / c < ν := by
  have h1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  rcases lt_or_ge c 2 with h2 | h2
  · exact lt_of_le_of_lt (tau0_ge_inv hc) (abe_invariant hc h2 h).2.2.2
  · have := (abe_nu_ge_one h2 h).2
    have : 1 / c < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith

noncomputable def iter (c : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, c - 1)
  | k + 1 => (c * (c - 1) * (iter c k).1,
      c * 1 * (c - 1) * (iter c k).2 / (1 + (c - 1) * (iter c k).2))

theorem iter_abe {c : ℝ} (hc : 1 < c) (hphi : 1 ≤ c * (c - 1)) (k : ℕ) :
    ABE c (iter c k).1 (iter c k).2 ∧ 1 ≤ (iter c k).1 ∧ 0 < (iter c k).2 := by
  induction k with
  | zero => exact ⟨ABE.base, le_refl 1, by simp [iter]; linarith⟩
  | succ k ih =>
    obtain ⟨hA, hμ, hν⟩ := ih
    have hside : (1 : ℝ) ≤ c * (c - 1) * (iter c k).1 := by nlinarith
    refine ⟨ABE.comp ABE.base hA hside, ?_, ?_⟩
    · simp only [iter]; nlinarith
    · simp only [iter]
      have : 0 < c - 1 := by linarith
      positivity

theorem iter_inv {c : ℝ} (hc : 1 < c) (hphi : 1 < c * (c - 1)) (k : ℕ) :
    1 / (iter c k).2 = 1 / tau0 c + (1 / (c - 1) - 1 / tau0 c) * (1 / (c * (c - 1))) ^ k := by
  have hcm : 0 < c - 1 := by linarith
  have hc0 : 0 < c := by linarith
  have ht : 0 < tau0 c := by
    unfold tau0
    rw [sub_pos, div_lt_iff₀ hcm]; linarith
  have htne : tau0 c ≠ 0 := ht.ne'
  have hpos := (iter_abe hc hphi.le k).2.2
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have hpos' := (iter_abe hc hphi.le k).2.2
    have hrec : 1 / (iter c (k + 1)).2 = (1 / (c * (c - 1))) * (1 / (iter c k).2) + 1 / c := by
      simp only [iter]
      have : (iter c k).2 ≠ 0 := hpos'.ne'
      have : c - 1 ≠ 0 := hcm.ne'
      have : c ≠ 0 := hc0.ne'
      have : 1 + (c - 1) * (iter c k).2 ≠ 0 := by positivity
      field_simp
    rw [hrec, ih hpos', pow_succ]
    have e : 1 / tau0 c = (c - 1) / (c * (c - 1) - 1) := by
      unfold tau0
      have : c - 1 ≠ 0 := hcm.ne'
      have : c * (c - 1) - 1 ≠ 0 := by linarith
      field_simp
    rw [e]
    have : c - 1 ≠ 0 := hcm.ne'
    have : c ≠ 0 := hc0.ne'
    have : c * (c - 1) - 1 ≠ 0 := by linarith
    field_simp
    ring

theorem exists_small_pair {c : ℝ} (hc : 1 < c) (hr : c < r7) : ∃ μ ν, ABE c μ ν ∧ ν < 1 / c := by
  have hcm : 0 < c - 1 := by linarith
  have hc0 : 0 < c := by linarith
  rcases lt_trichotomy (c * (c - 1)) 1 with hlt | heq | hgt
  · refine ⟨1, c - 1, ABE.base, ?_⟩
    rw [lt_div_iff₀ hc0]; linarith
  · refine ⟨c * (c - 1) * 1, c * 1 * (c - 1) * (c - 1) / (1 + (c - 1) * (c - 1)),
      ABE.comp ABE.base ABE.base (by linarith), ?_⟩
    have hd : 0 < 1 + (c - 1) * (c - 1) := by positivity
    rw [div_lt_div_iff₀ hd hc0]
    nlinarith
  · have hτ : tau0 c < 1 / c := by
      have := (tau_base_lt_iff_r7 hc).mpr hr
      unfold tau at this; unfold tau0; linarith
    have ht : 0 < tau0 c := by
      unfold tau0
      rw [sub_pos, div_lt_iff₀ hcm]; linarith
    have hgap : c < 1 / tau0 c := by
      rw [lt_div_iff₀ ht]
      have := mul_lt_mul_of_pos_left hτ hc0
      rwa [mul_one_div_cancel hc0.ne'] at this
    have ha0 : 0 < 1 / (c * (c - 1)) := by positivity
    have ha1 : 1 / (c * (c - 1)) < 1 := by rw [div_lt_one (by positivity)]; exact hgt
    set B := 1 / (c - 1) - 1 / tau0 c with hB
    rcases le_or_gt 0 B with hB0 | hB0
    · refine ⟨(iter c 0).1, (iter c 0).2, (iter_abe hc hgt.le 0).1, ?_⟩
      have hinv := iter_inv hc hgt 0
      have hpos := (iter_abe hc hgt.le 0).2.2
      have : c < 1 / (iter c 0).2 := by
        rw [hinv, pow_zero, mul_one]; linarith
      rw [lt_div_iff₀ hpos] at this
      rw [lt_div_iff₀ hc0]; linarith
    · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
        (div_pos (by linarith : 0 < 1 / tau0 c - c) (by linarith : 0 < -B)) ha1
      refine ⟨(iter c k).1, (iter c k).2, (iter_abe hc hgt.le k).1, ?_⟩
      have hinv := iter_inv hc hgt k
      have hpos := (iter_abe hc hgt.le k).2.2
      have hk' : -B * (1 / (c * (c - 1))) ^ k < 1 / tau0 c - c := by
        rw [lt_div_iff₀ (by linarith : 0 < -B)] at hk; linarith
      have : c < 1 / (iter c k).2 := by
        rw [hinv]; linarith
      rw [lt_div_iff₀ hpos] at this
      rw [lt_div_iff₀ hc0]; linarith

theorem pair_threshold {c : ℝ} (hc : 1 < c) : (∃ μ ν, ABE c μ ν ∧ ν < 1 / c) ↔ c < r7 := by
  constructor
  · rintro ⟨μ, ν, h, hν⟩
    by_contra hh
    push Not at hh
    linarith [no_small_pair hh h]
  · exact exists_small_pair hc

end PastaMath.SatBarriers
