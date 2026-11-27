-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The QBF_k alternation-trading calculus of Williams, "Alternation-trading
proofs, linear programming, and lower bounds" (TOCT 2013, §5; CMU full version, end of §3):
Speedup Rules 0/1 of Def. 4.1 unchanged, and a Slowdown Rule that removes up to k quantifier blocks
at once (hypothesis Σ_k TIME[n] ⊆ DTS[n^c]).

Lines `(st, a)`: `st` lists the after-superscripts of the blocks, innermost first (the input
superscript in front of the outermost block is 0; W13 has 1), `a` is the kernel exponent.  Guess
exponents are dropped (each is ≤ the after-superscript of its block).
* `speed`: Speedup Rule 1 (rule 0 when `st = []`): the innermost block's superscript becomes
  ≥ max(x, s), a new block with superscript ≥ s is opened, the kernel becomes ≥ a − x.
* `pop`: Slowdown Rule removing `rem` (1 ≤ |rem| ≤ k blocks):
  new kernel ≥ c·max(a, superscripts of the removed blocks, superscript in front of the outermost
  removed block).

Result: with q ∈ (0,1), k(1−q) = q²(2−q), c₀ = k/q (equivalently c₀³/k − c₀² − 2c₀ + k = 0, W13
Thm 5.1's polynomial), every path from ([], a₀) to an empty stack ends at ≥ a₀, for every c ≥ c₀.
Potential: min over groupings of the stack into pop groups of ≤ k blocks of a nested value built from
Λ(s,e) = min(e, max(q(s+e), c₀ s)) and L_r(s,e) = max(s, Λ(s,e)/(r+1)).
-/

noncomputable section

namespace PastaMath.QbfThreshold

/-- Threshold parameters: `q = k/c`, `c − k = q(2−q)`. -/
structure Par where
  k : ℕ
  c : ℝ
  q : ℝ
  hk : 1 ≤ k
  hq0 : 0 < q
  hq1 : q < 1
  hqc : q * c = k
  hu : c - k = q * (2 - q)

namespace Par
variable (P : Par)

theorem k_pos : (0 : ℝ) < P.k := by
  have := P.hk; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this

theorem k_ge_one : (1 : ℝ) ≤ P.k := by exact_mod_cast P.hk

theorem c_pos : 0 < P.c := by
  have h := P.hu; have := P.hq0; have := P.hq1; have := P.k_pos; nlinarith

theorem c_gt_k : (P.k : ℝ) < P.c := by
  have h := P.hu; have := P.hq0; have := P.hq1; nlinarith

theorem k_rel : (P.k : ℝ) * (1 - P.q) = P.q ^ 2 * (2 - P.q) := by
  have h1 := P.hqc; have h2 := P.hu
  have : P.q * (P.k + P.q * (2 - P.q)) = P.k := by rw [← h2]; ring_nf; linarith [h1]
  nlinarith

theorem u_le_one : P.c - P.k ≤ 1 := by rw [P.hu]; nlinarith [sq_nonneg (1 - P.q)]

/-- `(1 − q)(c − 2q) = q²`. -/
theorem rel2 : (1 - P.q) * (P.c - 2 * P.q) = P.q ^ 2 := by
  have h := P.k_rel; have h2 := P.hu
  have : P.c = P.k + P.q * (2 - P.q) := by linarith
  rw [this]; nlinarith

/-- W13 Thm 5.1's polynomial vanishes at `c`. -/
theorem poly_zero : P.c ^ 3 / P.k - P.c ^ 2 - 2 * P.c + P.k = 0 := by
  have hk := P.k_pos; have h1 := P.hqc; have h2 := P.hu
  have hq : P.q = P.k / P.c := by field_simp [P.c_pos.ne']; linarith
  have hc := P.c_pos
  rw [hq] at h2
  field_simp at h2 ⊢
  nlinarith [h2]

end Par

/-- Λ(s,e) = min(e, max(q(s+e), c s)). -/
def Lam (P : Par) (s e : ℝ) : ℝ := min e (max (P.q * (s + e)) (P.c * s))

/-- L_r(s,e) = max(s, Λ(s,e)/(r+1)). -/
def Lf (P : Par) (r : ℕ) (s e : ℝ) : ℝ := max s (Lam P s e / ((r : ℝ) + 1))

section arith
variable (P : Par)

theorem lam_mono {s s' e e' : ℝ} (hs : s ≤ s') (he : e ≤ e') : Lam P s e ≤ Lam P s' e' := by
  unfold Lam
  have hq := P.hq0.le; have hc := P.c_pos.le
  apply min_le_min he
  apply max_le_max
  · exact mul_le_mul_of_nonneg_left (by linarith) hq
  · exact mul_le_mul_of_nonneg_left hs hc

theorem lf_mono (r : ℕ) {s s' e e' : ℝ} (hs : s ≤ s') (he : e ≤ e') : Lf P r s e ≤ Lf P r s' e' := by
  unfold Lf
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  apply max_le_max hs
  exact div_le_div_of_nonneg_right (lam_mono P hs he) hr.le

theorem lam_le (s e : ℝ) : Lam P s e ≤ e := min_le_left _ _

theorem lf_le (r : ℕ) {s : ℝ} (hs : 0 ≤ s) (e : ℝ) : Lf P r s e ≤ max s e := by
  unfold Lf
  have hr : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  apply max_le (le_max_left _ _)
  have hl := lam_le P s e
  rcases le_or_gt (Lam P s e) 0 with h | h
  · have : Lam P s e / ((r : ℝ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (by linarith)
    linarith [le_max_left s e]
  · have : Lam P s e / ((r : ℝ) + 1) ≤ Lam P s e := div_le_self h.le hr
    linarith [le_max_right s e]

theorem lf_ge_lam (r : ℕ) (s e : ℝ) : Lam P s e / ((r : ℝ) + 1) ≤ Lf P r s e := le_max_right _ _

theorem lam_lip (s D x : ℝ) (hx : 0 ≤ x) : Lam P s (x + D) ≤ Lam P s D + x := by
  unfold Lam
  have hq := P.hq0.le; have hq1 := P.hq1.le
  rw [← min_add_add_right]
  apply min_le_min (by linarith)
  rw [← max_add_add_right]
  apply max_le_max _ (by linarith)
  nlinarith

/-- Parameter facts used by the key inequality. -/
theorem f3 : (P.c - P.k) * (P.c - P.q) = P.k := by
  have h1 := P.hqc; have h2 := P.hu; have h3 := P.k_rel
  rw [h2]
  have hc : P.c = P.k + P.q * (2 - P.q) := by linarith
  have : P.q * (2 - P.q) * (P.c - P.q) = (2 - P.q) * (P.q * P.c) - P.q ^ 2 * (2 - P.q) := by ring
  rw [this, h1]; nlinarith

theorem f5 : ((P.k : ℝ) + 1) * (P.c - P.k) ≤ P.c := by
  have h := P.u_le_one; have hk := P.k_pos
  have : ((P.k : ℝ) + 1) * (P.c - P.k) = P.c - P.k * (1 - (P.c - P.k)) := by ring
  rw [this]; nlinarith

theorem f6 : P.q * P.c ≤ P.c - P.q := by
  have h1 := P.hqc; have h2 := P.hu; have := P.hq0; have := P.hq1
  rw [h1]; nlinarith

theorem f8 : (P.k : ℝ) * (1 - P.q) = P.q * (P.c - P.k) := by rw [P.k_rel, P.hu]; ring

theorem cq_pos : 0 < P.c - P.q := by have := f6 P; have := P.hq0; have := P.c_pos; nlinarith

/-- Core of the key inequality, in plain variables. -/
theorem key_core {s x D h Pd K σ : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hσx : x ≤ σ) (hσs : s ≤ σ) (hσ : σ = x ∨ σ = s)
    (hPd : Pd = min D (max (P.q * (s + D)) (P.c * s)))
    (hh : h = min (x + D) (max (P.q * (s + (x + D))) (P.c * s)))
    (hK1 : P.c * σ ≤ K) (_hqK1 : (P.k : ℝ) * σ ≤ P.q * K) (hqK2 : Pd ≤ P.q * K) :
    h ≤ min K (max (P.q * (σ + K)) (P.c * σ)) := by
  have hq0 := P.hq0; have hq1 := P.hq1; have hc := P.c_pos; have hk := P.k_pos
  have F1 := P.hqc; have F3 := f3 P; have F5 := f5 P; have F6 := f6 P; have F7 := P.rel2
  have F8 := f8 P; have hcq := cq_pos P
  rcases le_or_gt h (P.c * σ) with hcs | hcs
  · exact le_min (le_trans hcs hK1) (le_trans hcs (le_max_right _ _))
  have hcs' : P.c * s < h := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hσs hc.le) hcs
  have hcx' : P.c * x < h := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hσx hc.le) hcs
  have hhe : h ≤ x + D := by rw [hh]; exact min_le_left _ _
  have hh2 : h ≤ P.q * (s + (x + D)) := by
    have : h ≤ max (P.q * (s + (x + D))) (P.c * s) := by rw [hh]; exact min_le_right _ _
    rcases le_total (P.q * (s + (x + D))) (P.c * s) with hm | hm
    · rw [max_eq_right hm] at this; linarith
    · rwa [max_eq_left hm] at this
  have hh0 : 0 ≤ h := le_trans (mul_nonneg hc.le hs) hcs'.le
  have m1 : P.c * h ≤ P.c * (P.q * (s + (x + D))) := mul_le_mul_of_nonneg_left hh2 hc.le
  have e1 : P.c * (P.q * (s + (x + D))) = P.q * (P.c * s) + P.k * (x + D) := by
    rw [← F1]; ring
  -- (A1) q h < D
  have hA1 : P.q * h < D := by
    have m2 : P.q * (P.c * s) < P.q * h := mul_lt_mul_of_pos_left hcs' hq0
    have r0 : (P.c - P.q) * h < P.k * (x + D) := by
      have : (P.c - P.q) * h = P.c * h - P.q * h := by ring
      rw [this]; linarith
    have r1 : (P.c - P.q) * h < (P.c - P.q) * ((P.c - P.k) * (x + D)) := by
      have : (P.k : ℝ) * (x + D) = (P.c - P.q) * ((P.c - P.k) * (x + D)) := by
        rw [show (P.c - P.q) * ((P.c - P.k) * (x + D)) = ((P.c - P.k) * (P.c - P.q)) * (x + D) by ring, F3]
      linarith
    have r2 : h < (P.c - P.k) * (x + D) := lt_of_mul_lt_mul_left r1 hcq.le
    have m3 : ((P.k : ℝ) + 1) * h ≤ ((P.k : ℝ) + 1) * ((P.c - P.k) * (x + D)) :=
      mul_le_mul_of_nonneg_left r2.le (by linarith)
    have m4 : ((P.k : ℝ) + 1) * (P.c - P.k) * (x + D) ≤ P.c * (x + D) :=
      mul_le_mul_of_nonneg_right F5 (by linarith)
    have e2 : P.c * (P.q * h) = P.k * h := by rw [← F1]; ring
    have m5 : P.c * (P.q * h + x) < P.c * (x + D) := by
      have : P.c * (P.q * h + x) = P.c * (P.q * h) + P.c * x := by ring
      have : ((P.k : ℝ) + 1) * ((P.c - P.k) * (x + D)) = ((P.k : ℝ) + 1) * (P.c - P.k) * (x + D) := by ring
      linarith
    have := lt_of_mul_lt_mul_left m5 hc.le
    linarith
  -- (A2) h < s + D
  have hA2 : h < s + D := by
    have m5 : P.q * (P.c * x) < P.q * h := mul_lt_mul_of_pos_left hcx' hq0
    have m6 : P.q * P.c * h ≤ (P.c - P.q) * h := mul_le_mul_of_nonneg_right F6 hh0
    have e3 : P.q * P.c * (s + D) = P.c * (P.q * (s + (x + D))) - P.q * (P.c * x) := by ring
    have : P.q * P.c * h < P.q * P.c * (s + D) := by
      have : (P.c - P.q) * h = P.c * h - P.q * h := by ring
      linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hPdq : P.q * h ≤ Pd := by
    rw [hPd]
    apply le_min hA1.le
    exact le_trans (mul_le_mul_of_nonneg_left hA2.le hq0.le) (le_max_left _ _)
  have hKh : h ≤ K := le_of_mul_le_mul_left (le_trans hPdq hqK2) hq0
  -- (B) h ≤ q (σ + K)
  have hB : h ≤ P.q * (σ + K) := by
    have eB : P.q * (σ + K) = P.q * σ + P.q * K := by ring
    rw [eB]
    have mx : P.q * x ≤ P.q * σ := mul_le_mul_of_nonneg_left hσx hq0.le
    have ms : P.q * s ≤ P.q * σ := mul_le_mul_of_nonneg_left hσs hq0.le
    rcases le_or_gt (P.q * (s + D)) Pd with hP | hP
    · have : P.q * (s + (x + D)) = P.q * x + P.q * (s + D) := by ring
      linarith
    have hPD : Pd = D := by
      rw [hPd] at hP ⊢
      rcases le_total D (max (P.q * (s + D)) (P.c * s)) with hm | hm
      · exact min_eq_left hm
      · rw [min_eq_right hm] at hP; linarith [le_max_left (P.q * (s + D)) (P.c * s)]
    have hDlt : D < P.q * (s + D) := by rw [hPD] at hP; exact hP
    rcases hσ with hσe | hσe
    · -- σ = x: contradiction
      exfalso
      have hsx : s ≤ x := hσe ▸ hσs
      have h1 : (1 - P.q) * D < P.q * x := by
        have : P.q * s ≤ P.q * x := mul_le_mul_of_nonneg_left hsx hq0.le
        have : P.q * (s + D) = P.q * s + P.q * D := by ring
        have : (1 - P.q) * D = D - P.q * D := by ring
        linarith
      have h2 : (P.c - 2 * P.q) * x < P.q * D := by
        have : P.q * s ≤ P.q * x := mul_le_mul_of_nonneg_left hsx hq0.le
        have : P.q * (s + (x + D)) = P.q * s + P.q * x + P.q * D := by ring
        have : (P.c - 2 * P.q) * x = P.c * x - 2 * (P.q * x) := by ring
        linarith
      have hc2 : 0 < 1 - P.q := by linarith
      have h3 : (1 - P.q) * ((P.c - 2 * P.q) * x) < (1 - P.q) * (P.q * D) :=
        mul_lt_mul_of_pos_left h2 hc2
      have h4 : P.q * ((1 - P.q) * D) < P.q * (P.q * x) := mul_lt_mul_of_pos_left h1 hq0
      have e4 : (1 - P.q) * ((P.c - 2 * P.q) * x) = P.q ^ 2 * x := by rw [← mul_assoc, F7]
      have e5 : (1 - P.q) * (P.q * D) = P.q * ((1 - P.q) * D) := by ring
      have e6 : P.q * (P.q * x) = P.q ^ 2 * x := by ring
      linarith
    · -- σ = s
      have hxs : x ≤ s := hσe ▸ hσx
      have g1 : (P.c - P.q) * s < P.q * (x + D) := by
        have : P.q * (s + (x + D)) = P.q * s + P.q * (x + D) := by ring
        have : (P.c - P.q) * s = P.c * s - P.q * s := by ring
        linarith
      -- c s < (c - k)(x + D)
      have g2 : P.c * s < (P.c - P.k) * (x + D) := by
        have hu0 : 0 < P.c - P.k := by have := P.c_gt_k; linarith
        have a1 : (P.c - P.k) * ((P.c - P.q) * s) < (P.c - P.k) * (P.q * (x + D)) :=
          mul_lt_mul_of_pos_left g1 hu0
        have a2 : (P.c - P.k) * ((P.c - P.q) * s) = P.k * s := by rw [← mul_assoc, F3]
        have a3 : P.c * (P.k * s) < P.c * ((P.c - P.k) * (P.q * (x + D))) :=
          mul_lt_mul_of_pos_left (a2 ▸ a1) hc
        have a4 : P.c * ((P.c - P.k) * (P.q * (x + D))) = P.k * ((P.c - P.k) * (x + D)) := by
          rw [← F1]; ring
        have a5 : P.c * (P.k * s) = P.k * (P.c * s) := by ring
        rw [a4, a5] at a3
        exact lt_of_mul_lt_mul_left a3 hk.le
      have g3 : P.k * x < (P.c - P.k) * D := by
        have : P.c * x ≤ P.c * s := mul_le_mul_of_nonneg_left hxs hc.le
        have : (P.c - P.k) * (x + D) = P.c * x - P.k * x + (P.c - P.k) * D := by ring
        linarith
      have g4 : P.q * (x + D) ≤ D := by
        have b1 : P.q * (P.k * x) ≤ P.q * ((P.c - P.k) * D) := mul_le_mul_of_nonneg_left g3.le hq0.le
        have b2 : P.q * ((P.c - P.k) * D) = P.k * ((1 - P.q) * D) := by
          rw [← mul_assoc, ← F8]; ring
        have b3 : P.k * (P.q * x) ≤ P.k * ((1 - P.q) * D) := by
          have : P.q * (P.k * x) = P.k * (P.q * x) := by ring
          linarith
        have := le_of_mul_le_mul_left b3 hk
        have : P.q * (x + D) = P.q * x + P.q * D := by ring
        have : (1 - P.q) * D = D - P.q * D := by ring
        linarith
      have : P.q * (s + (x + D)) = P.q * s + P.q * (x + D) := by ring
      linarith
  exact le_min hKh (le_trans hB (le_max_left _ _))

/-- The key inequality (one closed segment): Λ(s, x+D) ≤ Λ(max(x,s), K) when
K ≥ c·max(max(x,s), Λ(s,D)/k). -/
theorem key {s x D K : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hK : P.c * max (max x s) (Lam P s D / P.k) ≤ K) :
    Lam P s (x + D) ≤ Lam P (max x s) K := by
  have hq0 := P.hq0; have hc := P.c_pos; have hk := P.k_pos; have F1 := P.hqc
  have hK1 : P.c * max x s ≤ K := le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le) hK
  have hK2 : P.c * (Lam P s D / P.k) ≤ K :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le) hK
  have hqK1 : (P.k : ℝ) * max x s ≤ P.q * K := by
    have := mul_le_mul_of_nonneg_left hK1 hq0.le
    have e : P.q * (P.c * max x s) = P.k * max x s := by rw [← F1]; ring
    linarith
  have hqK2 : Lam P s D ≤ P.q * K := by
    have := mul_le_mul_of_nonneg_left hK2 hq0.le
    have e : P.q * (P.c * (Lam P s D / P.k)) = Lam P s D := by
      rw [show P.q * (P.c * (Lam P s D / P.k)) = (P.q * P.c) * (Lam P s D / P.k) by ring, F1]
      field_simp
    linarith
  have hσ : max x s = x ∨ max x s = s := by
    rcases le_total x s with h | h
    · exact Or.inr (max_eq_right h)
    · exact Or.inl (max_eq_left h)
  exact key_core P hs hx hD (le_max_left _ _) (le_max_right _ _) hσ rfl rfl hK1 hqK1 hqK2

theorem cast_km1 : (((P.k - 1 : ℕ) : ℝ) + 1) = P.k := by
  have := P.hk
  rw [Nat.cast_sub this]; push_cast; ring

/-- (S): one closed segment does not lower L_r. -/
theorem lf_S (r : ℕ) {s x D K : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hK : P.c * max (max x s) (Lf P (P.k - 1) s D) ≤ K) :
    Lf P r s (x + D) ≤ Lf P r (max x s) K := by
  have hc := P.c_pos
  have h1 : Lam P s D / P.k ≤ Lf P (P.k - 1) s D := by
    have := lf_ge_lam P (P.k - 1) s D; rwa [cast_km1 P] at this
  have hK' : P.c * max (max x s) (Lam P s D / P.k) ≤ K :=
    le_trans (mul_le_mul_of_nonneg_left (max_le_max le_rfl h1) hc.le) hK
  have hkey := key P hs hx hD hK'
  unfold Lf
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  exact max_le_max (le_max_right _ _) (div_le_div_of_nonneg_right hkey hr.le)

/-- (E): an extension does not lower L_r (r ≥ 1). -/
theorem lf_E {r : ℕ} (hr : 1 ≤ r) {s x D : ℝ} (hx : 0 ≤ x) :
    Lf P r s (x + D) ≤ max (max x s) (Lf P (r - 1) s D) := by
  have hcast : (((r - 1 : ℕ) : ℝ) + 1) = r := by rw [Nat.cast_sub hr]; push_cast; ring
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold Lf
  rw [hcast]
  apply max_le (le_trans (le_max_right x s) (le_max_left _ _))
  set Λ := Lam P s (x + D)
  have hl : Λ ≤ Lam P s D + x := lam_lip P s D x hx
  have hr0 : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  rcases le_or_gt (Λ / ((r : ℝ) + 1)) x with h | h
  · exact le_trans h (le_trans (le_max_left x s) (le_max_left _ _))
  · apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_right _ _)
    rw [div_le_div_iff₀ hr0 (by linarith)]
    rw [lt_div_iff₀ hr0] at h
    nlinarith

/-- First step from an empty stack: c·L_{k−1}(0,a) = a. -/
theorem top_eq {a : ℝ} (ha : 0 ≤ a) : P.c * Lf P (P.k - 1) 0 a = a := by
  have hq0 := P.hq0; have hq1 := P.hq1; have hk := P.k_pos; have F1 := P.hqc
  unfold Lf
  rw [cast_km1 P]
  have hL : Lam P 0 a = P.q * a := by
    unfold Lam
    rw [mul_zero, zero_add, max_eq_left (by positivity), min_eq_right]
    nlinarith
  rw [hL, max_eq_right (by positivity)]
  field_simp
  rw [← F1]; ring

end arith

/-! ### The calculus and the grouping potential -/

abbrev QLine := List ℝ × ℝ

def lmax : List ℝ → ℝ
  | [] => 0
  | b :: l => max b (lmax l)

def front : List ℝ → ℝ
  | [] => 0
  | b :: _ => b

/-- The QBF_k calculus (reduced form; see the module docstring). -/
inductive QStep (c : ℝ) (k : ℕ) : QLine → QLine → Prop
  | speed (st : List ℝ) (a x b₁ b₂ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₁ : max x (front st) ≤ b₁) (h₂ : front st ≤ b₂) (h₃ : a - x ≤ a₂) :
      QStep c k (st, a) (b₂ :: b₁ :: st.tail, a₂)
  | pop (rem rest : List ℝ) (a e : ℝ) (h1 : 1 ≤ rem.length) (h2 : rem.length ≤ k)
      (he : c * max a (max (lmax rem) (front rest)) ≤ e) :
      QStep c k (rem ++ rest, a) (rest, e)

/-- All superscripts and the kernel are nonnegative. -/
def NN (L : QLine) : Prop := (∀ b ∈ L.1, 0 ≤ b) ∧ 0 ≤ L.2

/-- Groupings of a stack into consecutive pop groups of 1..k blocks (innermost group first). -/
def Valid (k : ℕ) : List ℕ → List ℝ → Prop
  | [], st => st = []
  | h :: g, st => 1 ≤ h ∧ h ≤ k ∧ h ≤ st.length ∧ Valid k g (st.drop h)

/-- Value of a grouping. -/
def val (P : Par) : List ℝ → List ℕ → ℝ → ℝ
  | _, [], a => a
  | st, h :: g, a => val P (st.drop h) g
      (P.c * max (max (lmax (st.take h).tail) (front (st.drop h))) (Lf P (P.k - h) (front st) a))

theorem lmax_nonneg : ∀ l : List ℝ, 0 ≤ lmax l
  | [] => le_rfl
  | _ :: l => le_trans (lmax_nonneg l) (le_max_right _ _)

theorem front_le_lmax : ∀ l : List ℝ, front l ≤ lmax l
  | [] => le_rfl
  | _ :: _ => le_max_left _ _

theorem lmax_tail_le : ∀ l : List ℝ, lmax l.tail ≤ lmax l
  | [] => le_rfl
  | _ :: _ => le_max_right _ _

theorem front_nonneg {l : List ℝ} (h : ∀ b ∈ l, 0 ≤ b) : 0 ≤ front l := by
  cases l with
  | nil => exact le_rfl
  | cons b l => exact h b (List.mem_cons_self ..)

theorem valid_nil {k : ℕ} {g : List ℕ} (h : Valid k g []) : g = [] := by
  cases g with
  | nil => rfl
  | cons h' g => simp [Valid] at h; omega

theorem valid_len {k : ℕ} : ∀ (g : List ℕ) (st st' : List ℝ), st.length = st'.length →
    Valid k g st → Valid k g st'
  | [], st, st', hl, hv => by
      simp [Valid] at hv ⊢; subst hv; simp at hl; exact List.length_eq_zero_iff.mp hl.symm
  | h :: g, st, st', hl, hv => by
      obtain ⟨h1, h2, h3, h4⟩ := hv
      exact ⟨h1, h2, hl ▸ h3, valid_len g _ _ (by simp [hl]) h4⟩

theorem val_mono (P : Par) : ∀ (g : List ℕ) (st : List ℝ) {a a' : ℝ}, a ≤ a' →
    val P st g a ≤ val P st g a'
  | [], st, a, a', h => h
  | h :: g, st, a, a', ha => by
      simp only [val]
      apply val_mono P g
      apply mul_le_mul_of_nonneg_left _ P.c_pos.le
      exact max_le_max le_rfl (lf_mono P _ le_rfl ha)

theorem val_head (P : Par) (h : ℕ) (g : List ℕ) (rest : List ℝ) {s b a a' : ℝ} (h1 : 1 ≤ h)
    (hl : Lf P (P.k - h) s a ≤ Lf P (P.k - h) b a') :
    val P (s :: rest) (h :: g) a ≤ val P (b :: rest) (h :: g) a' := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  simp only [val, List.take_succ_cons, List.drop_succ_cons, List.tail_cons, front]
  apply val_mono P g
  exact mul_le_mul_of_nonneg_left (max_le_max le_rfl hl) P.c_pos.le

theorem step_nn {c : ℝ} (hc : 0 ≤ c) {k : ℕ} {L L' : QLine} (hs : QStep c k L L') (hn : NN L) :
    NN L' := by
  obtain ⟨hb, ha⟩ := hn
  cases hs with
  | speed st a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
      have hf := front_nonneg hb
      refine ⟨?_, by linarith⟩
      intro b hb'
      simp only [List.mem_cons] at hb'
      rcases hb' with rfl | rfl | hb'
      · linarith
      · linarith [le_max_left x (front st)]
      · exact hb b (List.mem_of_mem_tail hb')
  | pop rem rest a e h1 h2 he =>
      refine ⟨fun b hb' => hb b (List.mem_append_right _ hb'), ?_⟩
      exact le_trans (mul_nonneg hc (le_trans ha (le_max_left _ _))) he

/-- One step never lowers the potential: every grouping of the new line is dominated by some
grouping of the old line. -/
theorem step_pot (P : Par) {L L' : QLine} (hs : QStep P.c P.k L L') (hn : NN L) :
    ∀ g', Valid P.k g' L'.1 → ∃ g, Valid P.k g L.1 ∧ val P L.1 g L.2 ≤ val P L'.1 g' L'.2 := by
  have hc := P.c_pos
  obtain ⟨hb, ha⟩ := hn
  cases hs with
  | speed st a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    intro g' hv
    set s0 := front st with hs0
    have hf : 0 ≤ s0 := front_nonneg hb
    have hD : 0 ≤ a - x := by linarith
    have hb1 : max x s0 ≤ b₁ := h₁
    have hb10 : 0 ≤ b₁ := le_trans hx (le_trans (le_max_left _ _) hb1)
    set K := P.c * max b₁ (Lf P (P.k - 1) b₂ a₂) with hK
    have hS : ∀ r, Lf P r s0 a ≤ Lf P r b₁ K := by
      intro r
      have e : a = x + (a - x) := by ring
      have := lf_S P r hf hx hD (le_refl (P.c * max (max x s0) (Lf P (P.k - 1) s0 (a - x))))
      rw [← e] at this
      refine le_trans this (lf_mono P r hb1 ?_)
      apply mul_le_mul_of_nonneg_left _ hc.le
      exact max_le_max hb1 (lf_mono P _ h₂ h₃)
    have hE : ∀ r, 1 ≤ r → Lf P r s0 a ≤ max b₁ (Lf P (r - 1) b₂ a₂) := by
      intro r hr
      have e : a = x + (a - x) := by ring
      have := lf_E P hr (s := s0) (D := a - x) hx
      rw [← e] at this
      exact le_trans this (max_le_max hb1 (lf_mono P _ h₂ h₃))
    have htop : a = P.c * Lf P (P.k - 1) 0 a := (top_eq P ha).symm
    cases g' with
    | nil => simp [Valid] at hv
    | cons h' g'' =>
      obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
      match h', hv1, hv2, hv3, hv4 with
      | 1, _, _, _, hv4 =>
        simp only [List.drop_succ_cons, List.drop_zero] at hv4
        have hval : val P (b₂ :: b₁ :: st.tail) (1 :: g'') a₂ = val P (b₁ :: st.tail) g'' K := by
          simp only [val, List.take_succ_cons, List.take_zero, List.tail_cons, lmax,
            List.drop_succ_cons, List.drop_zero, front]
          rw [max_eq_right hb10]
        rw [hval]
        cases st with
        | nil =>
          simp only [List.tail_nil] at hv4 ⊢
          obtain ⟨h'', g3, rfl⟩ : ∃ h'' g3, g'' = h'' :: g3 := by
            cases g'' with
            | nil => simp [Valid] at hv4
            | cons h'' g3 => exact ⟨h'', g3, rfl⟩
          obtain ⟨w1, w2, w3, w4⟩ := hv4
          have hh1 : h'' = 1 := by simp at w3; omega
          subst hh1
          simp only [List.drop_succ_cons, List.drop_zero] at w4
          have := valid_nil w4; subst this
          refine ⟨[], rfl, ?_⟩
          simp only [val, List.take_succ_cons, List.take_zero, List.tail_cons, lmax,
            List.drop_succ_cons, List.drop_zero, front, max_self]
          calc a = P.c * Lf P (P.k - 1) 0 a := htop
            _ ≤ P.c * Lf P (P.k - 1) b₁ K := mul_le_mul_of_nonneg_left (hS _) hc.le
            _ ≤ P.c * max 0 (Lf P (P.k - 1) b₁ K) :=
                mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le
        | cons s rest =>
          simp only [List.tail_cons] at hv4 ⊢
          obtain ⟨h'', g3, rfl⟩ : ∃ h'' g3, g'' = h'' :: g3 := by
            cases g'' with
            | nil => simp [Valid] at hv4
            | cons h'' g3 => exact ⟨h'', g3, rfl⟩
          refine ⟨h'' :: g3, valid_len _ _ _ (by simp) hv4, ?_⟩
          exact val_head P h'' g3 rest hv4.1 (hS _)
      | n + 2, _, hk2, hlen, hv4 =>
        simp only [List.drop_succ_cons] at hv4
        have hval : val P (b₂ :: b₁ :: st.tail) ((n + 2) :: g'') a₂ =
            val P (st.tail.drop n) g'' (P.c * max (max (max b₁ (lmax (st.tail.take n)))
              (front (st.tail.drop n))) (Lf P (P.k - (n + 2)) b₂ a₂)) := by
          simp only [val, List.take_succ_cons, List.tail_cons, lmax, List.drop_succ_cons, front]
        rw [hval]
        have hr : 1 ≤ P.k - (n + 1) := by omega
        have hE' := hE _ hr
        have hsub : P.k - (n + 1) - 1 = P.k - (n + 2) := by omega
        rw [hsub] at hE'
        cases st with
        | nil =>
          simp only [List.tail_nil, List.length_cons, List.length_nil] at hv4 hlen ⊢
          have hn0 : n = 0 := by omega
          subst hn0
          have := valid_nil (by simpa using hv4); subst this
          refine ⟨[], rfl, ?_⟩
          simp only [val, List.take_zero, List.drop_zero, lmax, front]
          have hk1 : P.k - (0 + 1) = P.k - 1 := rfl
          rw [hk1] at hE'
          calc a = P.c * Lf P (P.k - 1) 0 a := htop
            _ ≤ P.c * max (max (max b₁ 0) 0) (Lf P (P.k - (0 + 2)) b₂ a₂) := by
                apply mul_le_mul_of_nonneg_left _ hc.le
                refine le_trans hE' (max_le_max ?_ le_rfl)
                exact le_trans (le_max_left _ _) (le_max_left _ _)
        | cons s rest =>
          simp only [List.tail_cons, List.length_cons] at hv4 hlen ⊢
          refine ⟨(n + 1) :: g'', ⟨by omega, by omega, by simp; omega, ?_⟩, ?_⟩
          · simpa [List.drop_succ_cons] using hv4
          · simp only [val, List.take_succ_cons, List.tail_cons, List.drop_succ_cons, front]
            apply val_mono P g''
            apply mul_le_mul_of_nonneg_left _ hc.le
            apply max_le
            · exact le_trans (max_le_max (le_max_right _ _) le_rfl) (le_max_left _ _)
            · refine le_trans hE' (max_le ?_ (le_max_right _ _))
              exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  | pop rem rest a e h1 h2 he =>
    intro g' hv
    refine ⟨rem.length :: g', ⟨h1, h2, by simp, by simpa using hv⟩, ?_⟩
    have ht : (rem ++ rest).take rem.length = rem := by simp
    have hd : (rem ++ rest).drop rem.length = rest := by simp
    show val P ((rem ++ rest).drop rem.length) g' _ ≤ _
    rw [ht, hd]
    apply val_mono P g'
    obtain ⟨b, t, rfl⟩ : ∃ b t, rem = b :: t := by
      cases rem with
      | nil => simp at h1
      | cons b t => exact ⟨b, t, rfl⟩
    have hb0 : 0 ≤ b := hb b (by simp)
    have hlf := lf_le P (P.k - (b :: t).length) hb0 a
    simp only [List.cons_append, front, List.tail_cons] at hlf ⊢
    refine le_trans ?_ he
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply max_le
    · apply max_le
      · exact le_trans (lmax_tail_le (b :: t)) (le_trans (le_max_left _ _) (le_max_right _ _))
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
    · refine le_trans hlf (max_le ?_ (le_max_left _ _))
      exact le_trans (front_le_lmax (b :: t)) (le_trans (le_max_left _ _) (le_max_right _ _))

/-! ### Paths -/

theorem qstep_restrict {c c₀ : ℝ} (hc : c₀ ≤ c) (_hc0 : 0 ≤ c₀) {k : ℕ} {L L' : QLine}
    (h : QStep c k L L') : QStep c₀ k L L' := by
  cases h with
  | speed st a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ => exact QStep.speed st a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃
  | pop rem rest a e h1 h2 he =>
    refine QStep.pop rem rest a e h1 h2 (le_trans ?_ he)
    have : 0 ≤ max a (max (lmax rem) (front rest)) :=
      le_trans (lmax_nonneg rem) (le_trans (le_max_left _ _) (le_max_right _ _))
    exact mul_le_mul_of_nonneg_right hc this

theorem path_nn {c : ℝ} (hc : 0 ≤ c) {k n : ℕ} {L : ℕ → QLine}
    (hstep : ∀ i < n, QStep c k (L i) (L (i + 1))) (h0 : NN (L 0)) : ∀ i ≤ n, NN (L i) := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih => intro hi; exact step_nn hc (hstep i (by omega)) (ih (by omega))

/-- Chain: every grouping of a later line is dominated by a grouping of the first line. -/
theorem chain (P : Par) {n : ℕ} {L : ℕ → QLine}
    (hstep : ∀ i < n, QStep P.c P.k (L i) (L (i + 1))) (h0 : NN (L 0)) :
    ∀ i ≤ n, ∀ g, Valid P.k g (L i).1 →
      ∃ g₀, Valid P.k g₀ (L 0).1 ∧ val P (L 0).1 g₀ (L 0).2 ≤ val P (L i).1 g (L i).2 := by
  have hnn := path_nn P.c_pos.le hstep h0
  intro i
  induction i with
  | zero => intro _ g hg; exact ⟨g, hg, le_rfl⟩
  | succ i ih =>
    intro hi g hg
    obtain ⟨g1, hg1, hle1⟩ := step_pot P (hstep i (by omega)) (hnn i (by omega)) g hg
    obtain ⟨g0, hg0, hle0⟩ := ih (by omega) g1 hg1
    exact ⟨g0, hg0, le_trans hle0 hle1⟩

/-- **Main theorem.** At any c ≥ c₀ (the threshold of `P`), every path from an empty stack
(DTS[n^{a₀}], a₀ ≥ 0) to an empty stack ends at an exponent ≥ a₀.  So the QBF_k calculus has no
refutation for c ≥ c₀. -/
theorem no_refutation (P : Par) {c : ℝ} (hc : P.c ≤ c) {n : ℕ} {L : ℕ → QLine}
    (hstep : ∀ i < n, QStep c P.k (L i) (L (i + 1))) (h0 : (L 0).1 = []) (ha0 : 0 ≤ (L 0).2)
    (hn : (L n).1 = []) : (L 0).2 ≤ (L n).2 := by
  have hstep' : ∀ i < n, QStep P.c P.k (L i) (L (i + 1)) :=
    fun i hi => qstep_restrict hc P.c_pos.le (hstep i hi)
  have hnn0 : NN (L 0) := ⟨by rw [h0]; simp, ha0⟩
  obtain ⟨g0, hg0, hle⟩ := chain P hstep' hnn0 n le_rfl [] (by rw [hn]; rfl)
  rw [h0] at hg0 hle
  have := valid_nil hg0; subst this
  simpa [val] using hle

theorem qstep_to_empty {c : ℝ} {k : ℕ} {L L' : QLine} (h : QStep c k L L') (he : L'.1 = []) :
    ∃ rem, L.1 = rem ∧ 1 ≤ rem.length ∧ rem.length ≤ k ∧ c * max L.2 (max (lmax rem) 0) ≤ L'.2 := by
  cases h with
  | speed st a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ => simp at he
  | pop rem rest a e h1 h2 he' =>
    simp only at he; subst he
    exact ⟨rem, by simp, h1, h2, by simpa [front] using he'⟩

/-- Above the threshold even non-strict refutations (final = initial, W13 Lemma 4.3's second case)
are impossible: a path of ≥ 1 step from DTS[n^{a₀}], a₀ > 0, ends at > a₀. -/
theorem no_refutation_strict (P : Par) {c : ℝ} (hc : P.c < c) {n : ℕ} {L : ℕ → QLine}
    (hn1 : 1 ≤ n) (hstep : ∀ i < n, QStep c P.k (L i) (L (i + 1))) (h0 : (L 0).1 = [])
    (ha0 : 0 < (L 0).2) (hn : (L n).1 = []) : (L 0).2 < (L n).2 := by
  have hstep' : ∀ i < n, QStep P.c P.k (L i) (L (i + 1)) :=
    fun i hi => qstep_restrict hc.le P.c_pos.le (hstep i hi)
  have hnn0 : NN (L 0) := ⟨by rw [h0]; simp, ha0.le⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨rem, hrem, h1, h2, he⟩ := qstep_to_empty (hstep m (by omega)) hn
  have hnn := path_nn P.c_pos.le hstep' hnn0 m (by omega)
  have hv : Valid P.k [rem.length] (L m).1 := by
    rw [hrem]; exact ⟨h1, h2, le_rfl, by simp [Valid]⟩
  obtain ⟨g0, hg0, hle⟩ := chain P hstep' hnn0 m (by omega) _ hv
  rw [h0] at hg0 hle
  have := valid_nil hg0; subst this
  simp only [val] at hle
  rw [hrem] at hle
  have hnn1 : ∀ b ∈ rem, 0 ≤ b := by rw [← hrem]; exact hnn.1
  obtain ⟨b, t, rfl⟩ : ∃ b t, rem = b :: t := by
    cases rem with
    | nil => simp at h1
    | cons b t => exact ⟨b, t, rfl⟩
  have hb0 : 0 ≤ b := hnn1 b (by simp)
  set X := max (L m).2 (max (lmax (b :: t)) 0) with hX
  have hvX : val P (b :: t) [(b :: t).length] (L m).2 ≤ P.c * X := by
    simp only [val, List.take_length, List.drop_length, front, List.tail_cons]
    apply mul_le_mul_of_nonneg_left _ P.c_pos.le
    apply max_le
    · exact max_le (le_trans (lmax_tail_le (b :: t)) (le_trans (le_max_left _ _) (le_max_right _ _)))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    · refine le_trans (lf_le P _ hb0 _) (max_le ?_ (le_max_left _ _))
      exact le_trans (front_le_lmax (b :: t)) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hX0 : 0 < X := by
    by_contra hneg; push Not at hneg
    have := le_trans hle hvX
    have : P.c * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos P.c_pos.le hneg
    simp only [val] at *; linarith
  have : P.c * X < c * X := mul_lt_mul_of_pos_right hc hX0
  linarith [le_trans hle hvX]
/-! ### Reachability form -/

theorem reach_restrict {c c₀ : ℝ} (hc : c₀ ≤ c) (hc0 : 0 ≤ c₀) {k : ℕ} {L L' : QLine}
    (h : Relation.ReflTransGen (QStep c k) L L') : Relation.ReflTransGen (QStep c₀ k) L L' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih (qstep_restrict hc hc0 hs)

theorem reach_nn {c : ℝ} (hc : 0 ≤ c) {k : ℕ} {L L' : QLine}
    (h : Relation.ReflTransGen (QStep c k) L L') (hn : NN L) : NN L' := by
  induction h with
  | refl => exact hn
  | tail _ hs ih => exact step_nn hc hs ih

theorem reach_pot (P : Par) {L L' : QLine} (h : Relation.ReflTransGen (QStep P.c P.k) L L')
    (hn : NN L) :
    ∀ g', Valid P.k g' L'.1 → ∃ g, Valid P.k g L.1 ∧ val P L.1 g L.2 ≤ val P L'.1 g' L'.2 := by
  induction h with
  | refl => intro g' hg; exact ⟨g', hg, le_rfl⟩
  | tail hr hs ih =>
    intro g' hg
    obtain ⟨g1, hg1, h1⟩ := step_pot P hs (reach_nn P.c_pos.le hr hn) g' hg
    obtain ⟨g0, hg0, h0⟩ := ih g1 hg1
    exact ⟨g0, hg0, le_trans h0 h1⟩

/-- Reachability form of `no_refutation`. -/
theorem no_refutation_reach (P : Par) {c : ℝ} (hc : P.c ≤ c) {a₀ a' : ℝ} (ha0 : 0 ≤ a₀)
    (h : Relation.ReflTransGen (QStep c P.k) ([], a₀) ([], a')) : a₀ ≤ a' := by
  have h' := reach_restrict hc P.c_pos.le h
  obtain ⟨g0, hg0, hle⟩ := reach_pot P h' ⟨by simp, ha0⟩ [] rfl
  have := valid_nil hg0; subst this
  simpa [val] using hle

end PastaMath.QbfThreshold

end
