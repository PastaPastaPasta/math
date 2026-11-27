-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

namespace PastaMath.SatBarriers

structure SlowEnvelope (c β : ℝ) (S : ℝ → ℝ → ℝ) : Prop where
  mono : ∀ {B B' M M' : ℝ}, B ≤ B' → M ≤ M' → S B M ≤ S B' M'
  lowerM : ∀ B M, c * M ≤ S B M
  lowerB : ∀ B M, B + β * (c - 1) * M ≤ S B M

theorem envelope_self {c β : ℝ} (hc : 1 ≤ c) (hβ : 0 ≤ β) :
    SlowEnvelope c β (fun B M => max (c * M) (B + β * (c - 1) * M)) where
  mono := by
    intro B B' M M' hB hM
    have h1 : c * M ≤ c * M' := mul_le_mul_of_nonneg_left hM (by linarith)
    have h2 : β * (c - 1) * M ≤ β * (c - 1) * M' :=
      mul_le_mul_of_nonneg_left hM (mul_nonneg hβ (by linarith))
    exact max_le_max h1 (by linarith)
  lowerM := fun _ _ => le_max_left _ _
  lowerB := fun _ _ => le_max_right _ _

theorem envelope_iInf {c β : ℝ} {ι : Type*} [Nonempty ι] {S : ι → ℝ → ℝ → ℝ}
    (hS : ∀ i, SlowEnvelope c β (S i)) :
    SlowEnvelope c β (fun B M => ⨅ i, S i B M) where
  mono := by
    intro B B' M M' hB hM
    have hbdd : BddBelow (Set.range fun i => S i B M) :=
      ⟨c * M, by rintro _ ⟨i, rfl⟩; exact (hS i).lowerM B M⟩
    exact ciInf_mono hbdd (fun i => (hS i).mono hB hM)
  lowerM := fun B M => le_ciInf (fun i => (hS i).lowerM B M)
  lowerB := fun B M => le_ciInf (fun i => (hS i).lowerB B M)

theorem envelope_min {c β : ℝ} {S T : ℝ → ℝ → ℝ} (hS : SlowEnvelope c β S)
    (hT : SlowEnvelope c β T) :
    SlowEnvelope c β (fun B M => min (S B M) (T B M)) where
  mono := fun hB hM => min_le_min (hS.mono hB hM) (hT.mono hB hM)
  lowerM := fun B M => le_min (hS.lowerM B M) (hT.lowerM B M)
  lowerB := fun B M => le_min (hS.lowerB B M) (hT.lowerB B M)

theorem envelope_restrict {c₀ c β : ℝ} {S : ℝ → ℝ → ℝ} (hc : c₀ ≤ c) (hβ : 0 ≤ β)
    (hS : SlowEnvelope c β S) :
    ∀ B M, 0 ≤ M → c₀ * M ≤ S B M ∧ B + β * (c₀ - 1) * M ≤ S B M := by
  intro B M hM
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_right hc hM) (hS.lowerM B M)
  · have : β * (c₀ - 1) * M ≤ β * (c - 1) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hβ) hM
    linarith [hS.lowerB B M]

theorem call_cost_lower {c J L : ℝ} (hc : 1 ≤ c) (hL : 0 < L) :
    J * L ^ (c - 1) ≤ (max J L) ^ c ∧ L ^ c ≤ (max J L) ^ c := by
  have hc1 : 0 ≤ c - 1 := by linarith
  have hsplit : ∀ y : ℝ, 0 < y → y ^ c = y * y ^ (c - 1) := by
    intro y hy
    have := Real.rpow_add hy 1 (c - 1)
    rw [show (1 : ℝ) + (c - 1) = c by ring, Real.rpow_one] at this
    exact this
  have hmax : 0 < max J L := lt_of_lt_of_le hL (le_max_right _ _)
  refine ⟨?_, Real.rpow_le_rpow hL.le (le_max_right _ _) (by linarith)⟩
  rw [hsplit _ hmax]
  have hp : L ^ (c - 1) ≤ (max J L) ^ (c - 1) :=
    Real.rpow_le_rpow hL.le (le_max_right _ _) hc1
  have hp0 : 0 ≤ L ^ (c - 1) := Real.rpow_nonneg hL.le _
  calc J * L ^ (c - 1) ≤ max J L * L ^ (c - 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
    _ ≤ max J L * (max J L) ^ (c - 1) := mul_le_mul_of_nonneg_left hp hmax.le

theorem decomposition_cost_lower {ι : Type*} (s : Finset ι) {c L : ℝ} (J : ι → ℝ)
    (hc : 1 ≤ c) (hL : 0 < L) :
    (∑ k ∈ s, J k) * L ^ (c - 1) ≤ ∑ k ∈ s, (max (J k) L) ^ c := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => (call_cost_lower (J := J k) hc hL).1

theorem decomposition_cost_single {ι : Type*} (s : Finset ι) {c L : ℝ} (J : ι → ℝ)
    (hc : 1 ≤ c) (hL : 0 < L) {k₀ : ι} (hk₀ : k₀ ∈ s) :
    L ^ c ≤ ∑ k ∈ s, (max (J k) L) ^ c := by
  have hnn : ∀ k ∈ s, 0 ≤ (max (J k) L) ^ c := fun k _ =>
    Real.rpow_nonneg (le_trans hL.le (le_max_right _ _)) _
  exact le_trans (call_cost_lower (J := J k₀) hc hL).2 (Finset.single_le_sum hnn hk₀)

theorem mixed_cost_lower {ι : Type*} (s : Finset ι) {c L D K K₁ : ℝ} (J : ι → ℝ)
    (hc : 1 ≤ c) (hL : 0 < L) (hD : 0 ≤ D) (hK₁ : 0 ≤ K₁) (hJ : ∀ k ∈ s, 0 ≤ J k)
    (hcover : K ≤ K₁ + ∑ k ∈ s, J k) :
    K * min D (L ^ (c - 1)) ≤ K₁ * D + ∑ k ∈ s, (max (J k) L) ^ c := by
  have hdec := decomposition_cost_lower s J hc hL
  have hsum : 0 ≤ ∑ k ∈ s, J k := Finset.sum_nonneg hJ
  have h0 : 0 ≤ min D (L ^ (c - 1)) := le_min hD (Real.rpow_nonneg hL.le _)
  have e1 : K₁ * min D (L ^ (c - 1)) ≤ K₁ * D := mul_le_mul_of_nonneg_left (min_le_left _ _) hK₁
  have e2 : (∑ k ∈ s, J k) * min D (L ^ (c - 1)) ≤ (∑ k ∈ s, J k) * L ^ (c - 1) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hsum
  have e3 : K * min D (L ^ (c - 1)) ≤ (K₁ + ∑ k ∈ s, J k) * min D (L ^ (c - 1)) :=
    mul_le_mul_of_nonneg_right hcover h0
  nlinarith

theorem ascent_run {q : ℕ} (α : ℕ → ℕ) (m : ℕ)
    (hasc : ∀ k, m + 1 ≤ k → k ≤ m + q → α (k - 1) < α k) :
    ∀ i, i ≤ q → α m + i ≤ α (m + i) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 := hasc (m + (i + 1)) (by omega) (by omega)
    have h3 : m + (i + 1) - 1 = m + i := by omega
    rw [h3] at h2
    omega

theorem exists_nonascent {q : ℕ} (α : ℕ → ℕ) (hα : ∀ k, α k < q) (m : ℕ) :
    ∃ k, m + 1 ≤ k ∧ k ≤ m + q ∧ α k ≤ α (k - 1) := by
  by_contra h
  push Not at h
  have := ascent_run α m h q le_rfl
  have := hα (m + q)
  omega

theorem nonascent_count {q T : ℕ} (α : ℕ → ℕ) (hα : ∀ k, α k < q) :
    (T - 1) / q ≤ ((Finset.Icc 1 (T - 1)).filter (fun k => α k ≤ α (k - 1))).card := by
  classical
  have hw : ∀ i, ∃ k, i * q + 1 ≤ k ∧ k ≤ i * q + q ∧ α k ≤ α (k - 1) :=
    fun i => exists_nonascent α hα (i * q)
  choose f hf using hw
  have hmaps : ∀ i ∈ Finset.range ((T - 1) / q),
      f i ∈ (Finset.Icc 1 (T - 1)).filter (fun k => α k ≤ α (k - 1)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨h1, h2, h3⟩ := hf i
    have hle : (i + 1) * q ≤ T - 1 := by
      have := Nat.div_mul_le_self (T - 1) q
      have : (i + 1) * q ≤ (T - 1) / q * q := Nat.mul_le_mul_right q hi
      omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, h3⟩
    have : i * q + q = (i + 1) * q := by ring
    omega
  have hinj : Set.InjOn f (Finset.range ((T - 1) / q)) := by
    intro i _ j _ hij
    obtain ⟨a1, a2, _⟩ := hf i
    obtain ⟨b1, b2, _⟩ := hf j
    rw [hij] at a1 a2
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : (i + 1) * q ≤ j * q := Nat.mul_le_mul_right q (by omega)
      have : i * q + q = (i + 1) * q := by ring
      omega
    · have : (j + 1) * q ≤ i * q := Nat.mul_le_mul_right q (by omega)
      have : j * q + q = (j + 1) * q := by ring
      omega
  have := Finset.card_le_card_of_injOn f hmaps hinj
  simpa using this

theorem bbr_witness_bound {W T s S₀ lT lq Z : ℝ}
    (hcount : T * s - 3 ≤ W + lT + S₀ * (lT + Z + lq) + (T - S₀) * s) :
    S₀ * (s - lT - Z - lq) - lT - 3 ≤ W := by
  nlinarith

end PastaMath.SatBarriers
