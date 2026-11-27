-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.BlackBox
import PastaMath.SatBarriers.EnvelopeBeta

namespace PastaMath.SatBarriers

def step10 (S : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (x : ℝ) : ℝ × ℝ :=
  (max x p.1, S (max x p.1) (max p.1 (p.2 - x)))

def run10 (S : ℝ → ℝ → ℝ) : ℝ × ℝ → List ℝ → ℝ × ℝ
  | p, [] => p
  | p, x :: xs => run10 S (step10 S p x) xs

theorem run10_fst_ge (S : ℝ → ℝ → ℝ) : ∀ (xs : List ℝ) (p : ℝ × ℝ), p.1 ≤ (run10 S p xs).1
  | [], _ => le_rfl
  | x :: xs, p => le_trans (le_max_right x p.1) (run10_fst_ge S xs (step10 S p x))

theorem run10_snd_ge {c β : ℝ} {S : ℝ → ℝ → ℝ} (hS : SlowEnvelope c β S) (hc : 0 ≤ c) :
    ∀ (xs : List ℝ) (p : ℝ × ℝ), xs ≠ [] → c * p.1 ≤ (run10 S p xs).2
  | [], _, h => absurd rfl h
  | [x], p, _ => by
    show c * p.1 ≤ S (max x p.1) (max p.1 (p.2 - x))
    exact le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hc) (hS.lowerM _ _)
  | x :: y :: ys, p, _ => by
    show c * p.1 ≤ (run10 S (step10 S p x) (y :: ys)).2
    have h1 := run10_snd_ge hS hc (y :: ys) (step10 S p x) (List.cons_ne_nil y ys)
    have h2 : c * p.1 ≤ c * (step10 S p x).1 :=
      mul_le_mul_of_nonneg_left (le_max_right x p.1) hc
    linarith

theorem lemma41_beta {c β b d x : ℝ} {S : ℝ → ℝ → ℝ} (hS : SlowEnvelope c β S)
    (hc1 : 1 < c) (hβ0 : 0 ≤ β) (hβ1 : β * (c - 1) ≤ 1)
    (hβc : (c - 1) * (1 + gam c β) ≤ c) (hd : 0 ≤ d) (xs : List ℝ)
    (hnr : (step10 S (b, d) x).2 < d) :
    max b ((c - 1) * d / c) ≤ (run10 S (b, d) (x :: xs)).1 ∧
      max (c * b) ((c - 1) * d) ≤ (run10 S (b, d) (x :: xs)).2 := by
  have hc0 : 0 < c := by linarith
  set p₁ := step10 S (b, d) x with hp₁
  have hrun : run10 S (b, d) (x :: xs) = run10 S p₁ xs := rfl
  have hM : c * (d - x) ≤ p₁.2 := by
    have := hS.lowerM (max x b) (max b (d - x))
    have h2 : c * (d - x) ≤ c * max b (d - x) := mul_le_mul_of_nonneg_left (le_max_right _ _) hc0.le
    simp only [hp₁, step10]
    linarith
  have hx : (c - 1) * d / c < x := by
    rw [div_lt_iff₀ hc0]
    nlinarith
  have hb₁ : max b ((c - 1) * d / c) ≤ p₁.1 := by
    simp only [hp₁, step10]
    exact max_le (le_max_right _ _) (le_trans hx.le (le_max_left _ _))
  have hfst := run10_fst_ge S xs p₁
  rw [hrun]
  refine ⟨le_trans hb₁ hfst, ?_⟩
  rcases xs with _ | ⟨y, ys⟩
  · show max (c * b) ((c - 1) * d) ≤ p₁.2
    have hd' : max (c * max b (d - x)) (x + β * (c - 1) * max b (d - x)) ≤ p₁.2 := by
      simp only [hp₁, step10]
      apply max_le (hS.lowerM _ _)
      have := hS.lowerB (max x b) (max b (d - x))
      have : x ≤ max x b := le_max_left _ _
      linarith
    exact max_le (step10_bound_beta hc1 hβ0 hβ1 hd hβc hd').2
      (step10_bound_beta hc1 hβ0 hβ1 hd hβc hd').1
  · have hlast := run10_snd_ge hS hc0.le (y :: ys) p₁ (List.cons_ne_nil y ys)
    have hbb : b ≤ p₁.1 := le_trans (le_max_left _ _) hb₁
    have hxd : (c - 1) * d < c * p₁.1 := by
      have : (c - 1) * d / c < p₁.1 := lt_of_lt_of_le (lt_of_lt_of_le hx (le_max_left x b)) le_rfl
      rw [div_lt_iff₀ hc0] at this
      linarith
    exact max_le (le_trans (mul_le_mul_of_nonneg_left hbb hc0.le) hlast)
      (le_trans hxd.le hlast)

theorem lemma41_r7 {β b d x : ℝ} {S : ℝ → ℝ → ℝ} (hS : SlowEnvelope r7 β S)
    (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hβ1 : β ≤ 1) (hd : 0 ≤ d) (xs : List ℝ)
    (hnr : (step10 S (b, d) x).2 < d) :
    max b ((r7 - 1) * d / r7) ≤ (run10 S (b, d) (x :: xs)).1 ∧
      max (r7 * b) ((r7 - 1) * d) ≤ (run10 S (b, d) (x :: xs)).2 := by
  obtain ⟨hi, _, _, _, hv, hβ0⟩ := beta_star_conditions hβ hβ1
  exact lemma41_beta hS one_lt_r7 hβ0 hv hi hd xs hnr

end PastaMath.SatBarriers
