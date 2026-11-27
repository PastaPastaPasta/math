-- SPDX-License-Identifier: Apache-2.0
import PastaMath.QbfThreshold.Cert

/-!
Summary for W13 §5 (QBF_k vs DTS[n^c]): kernel-checked intervals for the
threshold of the calculus `QStep c k`.

* Upper end (all k ≥ 1): no refutation once c > k and c³/k − c² − 2c + k ≥ 0, i.e. c ≥ c_k, the
  exponent of W13 Thm 5.1 (Table II: 2.903, 3.942, 4.962 for k = 2, 3, 4; 2cos(π/7) for k = 1).
* Lower end: explicit literal proofs (checked by `decide +kernel`) at
  k = 1: 7/4,  k = 2: 289/100,  k = 3: 393/100,  k = 4: 989/200.
W13's own construction (Thm 5.1) gives proofs for every c < c_k (paper argument, not formalised here).
-/

noncomputable section

namespace PastaMath.QbfThreshold

/-- Reachability form of the limit, stated with W13's polynomial. -/
theorem qbf_no_refutation_reach (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hck : (k : ℝ) < c)
    (hp : 0 ≤ c ^ 3 / k - c ^ 2 - 2 * c + k) {a₀ a' : ℝ} (ha0 : 0 ≤ a₀)
    (h : Relation.ReflTransGen (QStep c k) ([], a₀) ([], a')) : a₀ ≤ a' := by
  obtain ⟨P, rfl⟩ := exists_par k hk
  exact no_refutation_reach P (ge_of_poly P hck hp) ha0 h

def Refutes (c : ℝ) (k : ℕ) : Prop :=
  ∃ a₀ a' : ℝ, 0 ≤ a₀ ∧ a' < a₀ ∧ Relation.ReflTransGen (QStep c k) ([], a₀) ([], a')

theorem not_refutes (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hck : (k : ℝ) < c)
    (hp : 0 ≤ c ^ 3 / k - c ^ 2 - 2 * c + k) : ¬ Refutes c k := by
  rintro ⟨a₀, a', ha0, hlt, h⟩
  exact absurd (qbf_no_refutation_reach k hk hck hp ha0 h) (not_le.mpr hlt)

theorem refutes_of_check {c : ℚ} (hc : 0 ≤ c) {k : ℕ} {a0 : ℚ} {ops : List Op}
    (h : checkL c k a0 ops = true) : Refutes (c : ℝ) k := by
  obtain ⟨a', hlt, ha0, hr⟩ := checkL_sound hc h
  exact ⟨a0, a', ha0, hlt, hr⟩

theorem refutes_k1 : Refutes ((7 / 4 : ℚ) : ℝ) 1 := refutes_of_check (by norm_num) qcert1_ok
theorem refutes_k2 : Refutes ((289 / 100 : ℚ) : ℝ) 2 := refutes_of_check (by norm_num) qcert2_ok
theorem refutes_k3 : Refutes ((393 / 100 : ℚ) : ℝ) 3 := refutes_of_check (by norm_num) qcert3_ok
theorem refutes_k4 : Refutes ((989 / 200 : ℚ) : ℝ) 4 := refutes_of_check (by norm_num) qcert4_ok

/-- Refutability is downward closed in c. -/
theorem refutes_mono {c c' : ℝ} (hc : c' ≤ c) (hc0 : 0 ≤ c') {k : ℕ} (h : Refutes c k) :
    Refutes c' k := by
  obtain ⟨a₀, a', ha0, hlt, hr⟩ := h
  exact ⟨a₀, a', ha0, hlt, reach_restrict hc hc0 hr⟩

/-- k = 2: the threshold of the calculus lies in [2.89, c₂], c₂ ≈ 2.90321 the root of
c³/2 − c² − 2c + 2 in (2, 3). -/
theorem interval_k2 :
    (∀ c : ℝ, 0 ≤ c → c ≤ 289 / 100 → Refutes c 2) ∧
    (∀ c : ℝ, 2 < c → 0 ≤ c ^ 3 / 2 - c ^ 2 - 2 * c + 2 → ¬ Refutes c 2) := by
  refine ⟨fun c h0 h1 => refutes_mono (by push_cast; linarith) h0 refutes_k2, fun c h1 h2 => ?_⟩
  exact not_refutes 2 (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem interval_k3 :
    (∀ c : ℝ, 0 ≤ c → c ≤ 393 / 100 → Refutes c 3) ∧
    (∀ c : ℝ, 3 < c → 0 ≤ c ^ 3 / 3 - c ^ 2 - 2 * c + 3 → ¬ Refutes c 3) := by
  refine ⟨fun c h0 h1 => refutes_mono (by push_cast; linarith) h0 refutes_k3, fun c h1 h2 => ?_⟩
  exact not_refutes 3 (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem interval_k4 :
    (∀ c : ℝ, 0 ≤ c → c ≤ 989 / 200 → Refutes c 4) ∧
    (∀ c : ℝ, 4 < c → 0 ≤ c ^ 3 / 4 - c ^ 2 - 2 * c + 4 → ¬ Refutes c 4) := by
  refine ⟨fun c h0 h1 => refutes_mono (by push_cast; linarith) h0 refutes_k4, fun c h1 h2 => ?_⟩
  exact not_refutes 4 (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

/-- k = 1 (SAT): threshold in [7/4, 2cos(π/7)]. -/
theorem interval_k1 :
    (∀ c : ℝ, 0 ≤ c → c ≤ 7 / 4 → Refutes c 1) ∧ (∀ c : ℝ, r7 ≤ c → ¬ Refutes c 1) := by
  refine ⟨fun c h0 h1 => refutes_mono (by push_cast; linarith) h0 refutes_k1, fun c hc => ?_⟩
  rintro ⟨a₀, a', ha0, hlt, h⟩
  obtain ⟨P, hP⟩ := exists_par 1 le_rfl
  have hPc := par_one_eq_r7 P hP
  have h' : Relation.ReflTransGen (QStep c P.k) ([], a₀) ([], a') := by rw [hP]; exact h
  exact absurd (no_refutation_reach P (hPc ▸ hc) ha0 h') (not_le.mpr hlt)

/-- Consistency: the certified values lie below W13's exponents (p_k < 0 there). -/
theorem cert_below : ((289 : ℝ) / 100) ^ 3 / 2 - (289 / 100) ^ 2 - 2 * (289 / 100) + 2 < 0 ∧
    ((393 : ℝ) / 100) ^ 3 / 3 - (393 / 100) ^ 2 - 2 * (393 / 100) + 3 < 0 ∧
    ((989 : ℝ) / 200) ^ 3 / 4 - (989 / 200) ^ 2 - 2 * (989 / 200) + 4 < 0 := by
  norm_num

end PastaMath.QbfThreshold

end
