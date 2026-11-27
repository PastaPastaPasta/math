-- SPDX-License-Identifier: Apache-2.0
import PastaMath.QbfThreshold.Calculus
import PastaMath.QbfThreshold.Cubic
import Mathlib.Topology.Order.IntermediateValue

/-!
Threshold existence and the statement in terms of W13 Thm 5.1's
polynomial p_k(c) = c³/k − c² − 2c + k.

* `exists_par`: for every k ≥ 1 the threshold parameters exist (q ∈ (0,1) root of
  q²(2−q) = k(1−q), c₀ = k/q).
* `ge_of_poly`: if c > k and p_k(c) ≥ 0 then c ≥ c₀.
* `qbf_no_refutation`: for c > k with p_k(c) ≥ 0 (i.e. c ≥ W13's exponent c_k), the QBF_k calculus
  has no refutation; `qbf_no_refutation_strict`: if p_k(c) > 0 not even a non-strict one.
* `sat_no_refutation`: k = 1, c ≥ 2cos(π/7) (Buss–Williams' theorem, for this calculus).
-/

noncomputable section

namespace PastaMath.QbfThreshold

open Set

theorem exists_par (k : ℕ) (hk : 1 ≤ k) : ∃ P : Par, P.k = k := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let f : ℝ → ℝ := fun q => q ^ 2 * (2 - q) - k * (1 - q)
  have hf : ContinuousOn f (Icc 0 1) := by
    apply Continuous.continuousOn; fun_prop
  have h0 : f 0 < 0 := by simp [f]; linarith
  have h1 : 0 < f 1 := by simp [f]
  obtain ⟨q, ⟨hq0, hq1⟩, hfq⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hf ⟨h0, h1⟩
  have hfq' : q ^ 2 * (2 - q) = k * (1 - q) := by simp only [f] at hfq; linarith
  refine ⟨⟨k, k / q, q, hk, hq0, hq1, by field_simp, ?_⟩, rfl⟩
  field_simp
  nlinarith [hfq']

theorem c_sq (P : Par) : P.c ^ 2 = P.k * (P.c + 2 - P.q) := by
  have h1 := P.hqc; have h2 := P.hu
  have : P.c ^ 2 = P.c * (P.k + P.q * (2 - P.q)) := by rw [sq]; congr 1; linarith
  rw [this]
  have e : P.c * (P.k + P.q * (2 - P.q)) = P.c * P.k + (P.q * P.c) * (2 - P.q) := by ring
  rw [e, h1]; ring

theorem ge_of_poly (P : Par) {c : ℝ} (hck : (P.k : ℝ) < c)
    (hp : 0 ≤ c ^ 3 / P.k - c ^ 2 - 2 * c + P.k) : P.c ≤ c := by
  by_contra hlt'
  have hlt : c < P.c := not_le.mp hlt'
  have hk := P.k_pos; have hq1 := P.hq1; have hc0 := P.c_gt_k
  have hz := P.poly_zero
  have hcs := c_sq P
  -- p(c) - p(c0) = (c - c0) * B with B > 0
  set c0 := P.c
  have hB : 0 < (c ^ 2 + c * c0 + c0 ^ 2) / P.k - c - c0 - 2 := by
    have e1 : c ≤ c ^ 2 / P.k := by rw [le_div_iff₀ hk]; nlinarith
    have e2 : c0 ≤ c * c0 / P.k := by rw [le_div_iff₀ hk]; nlinarith
    have e3 : c0 ^ 2 / P.k = c0 + 2 - P.q := by rw [hcs]; field_simp
    have : (c ^ 2 + c * c0 + c0 ^ 2) / P.k = c ^ 2 / P.k + c * c0 / P.k + c0 ^ 2 / P.k := by ring
    have hqc0 : P.q < c0 := by linarith [P.k_ge_one]
    linarith
  have hdiff : c ^ 3 / P.k - c ^ 2 - 2 * c + P.k - (c0 ^ 3 / P.k - c0 ^ 2 - 2 * c0 + P.k) =
      (c - c0) * ((c ^ 2 + c * c0 + c0 ^ 2) / P.k - c - c0 - 2) := by
    field_simp; ring
  have : (c - c0) * ((c ^ 2 + c * c0 + c0 ^ 2) / P.k - c - c0 - 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hB
  linarith

/-- **QBF_k calculus limit.** For k ≥ 1 and c > k with c³/k − c² − 2c + k ≥ 0, every path of the
calculus from DTS[n^{a₀}] (a₀ ≥ 0) back to a DTS line ends at an exponent ≥ a₀. -/
theorem qbf_no_refutation (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hck : (k : ℝ) < c)
    (hp : 0 ≤ c ^ 3 / k - c ^ 2 - 2 * c + k) {n : ℕ} {L : ℕ → QLine}
    (hstep : ∀ i < n, QStep c k (L i) (L (i + 1))) (h0 : (L 0).1 = []) (ha0 : 0 ≤ (L 0).2)
    (hn : (L n).1 = []) : (L 0).2 ≤ (L n).2 := by
  obtain ⟨P, rfl⟩ := exists_par k hk
  exact no_refutation P (ge_of_poly P hck hp) hstep h0 ha0 hn

/-- Strictly above W13's exponent even non-strict refutations are impossible. -/
theorem qbf_no_refutation_strict (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hck : (k : ℝ) < c)
    (hp : 0 < c ^ 3 / k - c ^ 2 - 2 * c + k) {n : ℕ} {L : ℕ → QLine} (hn1 : 1 ≤ n)
    (hstep : ∀ i < n, QStep c k (L i) (L (i + 1))) (h0 : (L 0).1 = []) (ha0 : 0 < (L 0).2)
    (hn : (L n).1 = []) : (L 0).2 < (L n).2 := by
  obtain ⟨P, rfl⟩ := exists_par k hk
  have hle := ge_of_poly P hck hp.le
  have hne : P.c ≠ c := by
    intro h; have := P.poly_zero; rw [h] at this; linarith
  exact no_refutation_strict P (lt_of_le_of_ne hle hne) hn1 hstep h0 ha0 hn

/-- k = 1: the threshold parameter is 2cos(π/7). -/
theorem par_one_eq_r7 (P : Par) (h1 : P.k = 1) : P.c = r7 := by
  have hz := P.poly_zero
  have hc1 : (1 : ℝ) ≤ P.c := by have := P.c_gt_k; rw [h1] at this; push_cast at this; linarith
  rw [h1] at hz; push_cast at hz
  apply (cub_eq_zero_iff hc1).mp
  unfold cub; linarith

/-- k = 1 (SAT vs DTS, W13 Def. 4.1 with the literal slowdown cost): no refutation for c ≥ 2cos(π/7). -/
theorem sat_no_refutation {c : ℝ} (hc : r7 ≤ c) {n : ℕ} {L : ℕ → QLine}
    (hstep : ∀ i < n, QStep c 1 (L i) (L (i + 1))) (h0 : (L 0).1 = []) (ha0 : 0 ≤ (L 0).2)
    (hn : (L n).1 = []) : (L 0).2 ≤ (L n).2 := by
  obtain ⟨P, hP⟩ := exists_par 1 le_rfl
  have hPc := par_one_eq_r7 P hP
  have hstep' : ∀ i < n, QStep c P.k (L i) (L (i + 1)) := by rw [hP]; exact hstep
  exact no_refutation P (hPc ▸ hc) hstep' h0 ha0 hn

end PastaMath.QbfThreshold

end
