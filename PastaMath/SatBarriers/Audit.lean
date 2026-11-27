-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Bootstrap
import PastaMath.SatBarriers.LocalizedMax

/-!
Non-strict refutations and general-c derived lower bounds.

* W13 Lemma 4.3 accepts normal-form proofs DTS[n^a] ⊆ … ⊆ DTS[n^{a'}] with a' = a (and ≥ one
  quantified line) as contradictions. `RefutesWith` / `LRefutesX` only exclude a' < a.
  `no_refutation_nonstrict` (Step, c ≥ r, β ≥ β*) and `no_refutation_locX_nonstrict`
  (LStepX at β = 1, c > r) exclude the non-strict case too, for a > 0.
* Derived single-block lower bound: `segment_gen`,
  `ach_inv_one` and `derived_ns_lower` prove it for every c ∈ [r, 2) in BW's system with the
  β = 1 envelope (R2 and C1): a derivation of ⁰∃^{s}DTS(v) from DTS(a) has v ≥ ν*(c)·a with
  ν*(c) = tau0 c = c − 1/(c−1), strictly when a > 0.
-/

namespace PastaMath.SatBarriers
namespace AU

open BS

/-- `segment` (Derivation.lean) at a general c, under exactly the hypotheses `combine` uses. -/
theorem segment_gen {c β : ℝ} (hc1 : 1 < c) (hβ0 : 0 ≤ β) (hβ1' : β * (c - 1) ≤ 1)
    (hβc : (c - 1) * (1 + gam c β) ≤ c) (L : ℕ → RLine) :
    ∀ len p k : ℕ, (∀ i, p ≤ i → i < p + len → Step c β (L i) (L (i + 1))) →
      (∀ i, p ≤ i → i ≤ p + len → k + 1 ≤ (L i).1.length ∧ 0 ≤ (L i).2) →
      (L p).1.length = k + 1 → (L (p + len)).1.length = k + 1 →
      Concl c β (top (L p).1) (L p).2 (top (L (p + len)).1) (L (p + len)).2 := by
  have hpos := fun μ ν (h : Ach c β μ ν) => ach_pos hc1 hβ0 hβ1' h
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
  intro p k hstep hdep hp hq
  rcases Nat.eq_zero_or_pos len with h0 | hlen
  · subst h0
    exact Or.inl ⟨le_rfl, le_rfl⟩
  have hs0 := hstep p le_rfl (by omega)
  rcases step_inv hs0 with ⟨h1, -, -⟩ | ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, e0, e1⟩ |
    ⟨b, e0, -, -⟩ | ⟨hl, hle, ha⟩
  · rw [h1] at hp; simp at hp
  · have hbs : bs.length = k := by
      rw [e0] at hp; simp only [List.length_append, List.length_singleton] at hp; omega
    have hl1 : (L (p + 1)).1.length = k + 2 := by
      rw [e1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    classical
    have hex : ∃ j, p + 1 ≤ j ∧ j ≤ p + len ∧ (L j).1.length = k + 1 :=
      ⟨p + len, by omega, le_rfl, hq⟩
    obtain ⟨hm1, hm2, hm3⟩ := Nat.find_spec hex
    have hmin : ∀ j, p + 1 ≤ j → j < Nat.find hex → k + 2 ≤ (L j).1.length := by
      intro j hj1 hj2
      have h1 := Nat.find_min hex hj2
      have h2 := (hdep j (by omega) (by omega)).1
      by_contra hcon
      exact h1 ⟨hj1, by omega, by omega⟩
    set m0 := Nat.find hex with hm0
    have hm0p : p + 2 ≤ m0 := by
      by_contra hcon
      have : m0 = p + 1 := by omega
      rw [this, hl1] at hm3; omega
    have hsA := hstep (m0 - 1) (by omega) (by omega)
    rw [show m0 - 1 + 1 = m0 by omega] at hsA
    have hlA : (L (m0 - 1)).1.length = k + 2 := by
      have h1 := hmin (m0 - 1) (by omega) (by omega)
      have h2 := (step_len hsA).2
      omega
    rcases step_inv hsA with ⟨h1, -, -⟩ | ⟨bs', b', x', b₁', b₂', -, -, -, -, -, f0, f1⟩ |
      ⟨y, f0, hu1, hu2⟩ | ⟨f0, -, -⟩
    · rw [h1] at hlA; simp at hlA
    · rw [f1] at hm3; rw [f0] at hlA
      simp only [List.length_append, List.length_cons, List.length_nil] at hm3 hlA
      omega
    · have hA := ih (m0 - 1 - (p + 1)) (by omega) (p + 1) (k + 1)
        (fun i h1 h2 => hstep i (by omega) (by omega))
        (fun i h1 h2 => ⟨hmin i h1 (by omega), (hdep i (by omega) (by omega)).2⟩) hl1 (by
          rw [show p + 1 + (m0 - 1 - (p + 1)) = m0 - 1 by omega]; exact hlA)
      rw [show p + 1 + (m0 - 1 - (p + 1)) = m0 - 1 by omega] at hA
      have hB := ih (p + len - m0) (by omega) m0 k
        (fun i h1 h2 => hstep i (by omega) (by omega))
        (fun i h1 h2 => hdep i (by omega) (by omega)) hm3 (by
          rw [show m0 + (p + len - m0) = p + len by omega]; exact hq)
      rw [show m0 + (p + len - m0) = p + len by omega] at hB
      have htopA : top (L (p + 1)).1 = b₂ := by
        rw [e1, show bs ++ [b₁, b₂] = (bs ++ [b₁]) ++ [b₂] by simp, top_concat]
      have htopY : top (L (m0 - 1)).1 = y := by rw [f0, top_concat]
      rw [htopA, htopY] at hA
      have hmono : ∀ j, j ≤ m0 - 1 - (p + 1) →
          (L (p + 1)).1.getD k 0 ≤ (L (p + 1 + j)).1.getD k 0 := by
        intro j
        induction j with
        | zero => intro _; exact le_rfl
        | succ j ihj =>
          intro hj
          have hs := hstep (p + 1 + j) (by omega) (by omega)
          have := step_getD_mono hs (hmin (p + 1 + j) (by omega) (by omega))
            (hmin (p + 1 + j + 1) (by omega) (by omega))
          exact le_trans (ihj (by omega)) this
      have hX1 : (L (p + 1)).1.getD k 0 = b₁ := by
        rw [e1, List.getD_append_right _ _ _ _ (by omega), hbs, Nat.sub_self]; rfl
      have hX2 : (L (m0 - 1)).1.getD k 0 = top (L m0).1 := by
        rw [f0, List.getD_append _ _ _ _ (by omega), top_eq_getD hm3]
      have hXX := hmono (m0 - 1 - (p + 1)) le_rfl
      rw [show p + 1 + (m0 - 1 - (p + 1)) = m0 - 1 by omega, hX1, hX2] at hXX
      have hbtop : top (L p).1 = b := by rw [e0, top_concat]
      rw [hbtop]
      exact Or.inr (combine hc1 hβ0 hβ1' hβc (hdep p le_rfl (by omega)).2 hx hxa
        (le_trans h₁ hXX) h₂ h₃ hA hu1 hu2 hB)
    · rw [f0] at hm3; omega
  · have := (hdep (p + 1) (by omega) (by omega)).1
    rw [e0] at hp
    simp only [List.length_append, List.length_singleton] at hp this
    omega
  · have hl1 : (L (p + 1)).1.length = k + 1 := by rw [hl, hp]
    have hrest := ih (len - 1) (by omega) (p + 1) k
      (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => hdep i (by omega) (by omega)) hl1 (by
        rw [show p + 1 + (len - 1) = p + len by omega]; exact hq)
    rw [show p + 1 + (len - 1) = p + len by omega] at hrest
    have htop : top (L p).1 ≤ top (L (p + 1)).1 := by
      rw [top_eq_getD hp, top_eq_getD hl1]; exact hle k
    exact concl_mono (by linarith) hpos htop ha hrest

theorem gam_one (c : ℝ) : gam c 1 = 1 := by unfold gam; ring

/-- BW's invariant for the β = 1 pair closure at every c ∈ [r, 2). -/
theorem ach_inv_one {c : ℝ} (hc : r7 ≤ c) (hc2 : c < 2) {μ ν : ℝ} (h : Ach c 1 μ ν) :
    Inv c μ ν := by
  have hc1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  have hcub : 0 ≤ cub c := (cub_nonneg_iff hc1.le).mpr hc
  have hγ : 0 < gam c 1 := by rw [gam_one]; norm_num
  have hii : c * (2 - c) ≤ 1 * (c - 1) := by
    unfold cub at hcub
    have : 0 < c * (c ^ 2 - c - 1) := by nlinarith
    have h3 : 0 < c ^ 2 - c - 1 := by
      by_contra hn; push Not at hn; nlinarith
    nlinarith
  have hiii : gam c 1 * tau0 c ≤ c - 1 := by
    rw [gam_one, one_mul]; unfold tau0
    have : 1 ≤ 1 / (c - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith
  induction h with
  | base => exact inv_base hc hc2
  | big hμ hν => exact inv_big hc hc2 hμ hν
  | dbeta _ ih => exact inv_dbeta hc hγ hii hiii ih
  | @comp μ₁ ν₁ μ₂ ν₂ _ _ ih1 ih2 =>
    have hν1 : 0 < ν₁ := ih1.2.1
    have hpos : 0 < c * ν₁ := by positivity
    set μ₂' := max μ₂ (μ₁ / (c * ν₁)) with hμ₂'
    have h2' : Inv c μ₂' ν₂ := inv_weaken hc ih2 (le_max_left _ _) le_rfl
    have hside : μ₁ ≤ c * ν₁ * μ₂' := by
      have : μ₁ = c * ν₁ * (μ₁ / (c * ν₁)) := by field_simp
      calc μ₁ = c * ν₁ * (μ₁ / (c * ν₁)) := this
        _ ≤ c * ν₁ * μ₂' := mul_le_mul_of_nonneg_left (le_max_right _ _) hpos.le
    have hres := inv_comp hc ih1 h2' hside
    have heq : c * ν₁ * μ₂' = max μ₁ (c * ν₁ * μ₂) := by
      rw [hμ₂', mul_max_of_nonneg _ _ hpos.le, max_comm]
      congr 1
      field_simp
    rw [heq] at hres
    exact hres

/-- The level-1 segment of a derivation from DTS(a) to ⁰∃^{s}DTS(v), at any c ∈ (1, 2]. -/
theorem derived_concl {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) {n : ℕ} {L : ℕ → RLine} {a s v : ℝ}
    (h : DerivesFrom (Step c 1) n L a) (hnn : ∀ i, i ≤ n → 0 ≤ (L i).2)
    (hN : L n = ([s], v)) : Concl c 1 0 a s v := by
  have hL1 := first_is_init h
  obtain ⟨hn, h0, ha, hs, hne⟩ := h
  have hseg := segment_gen hc1 zero_le_one (by linarith) (by rw [gam_one]; linarith) L
    (n - 1) 1 0 (fun i h1 h2 => hs i (by omega))
    (fun i h1 h2 => ⟨by
      have := hne i (by omega) (by omega)
      exact Nat.one_le_iff_ne_zero.mpr (fun h => this (List.length_eq_zero_iff.mp h)),
      hnn i (by omega)⟩)
    (by rw [hL1]; rfl) (by rw [show 1 + (n - 1) = n by omega, hN]; rfl)
  rw [show 1 + (n - 1) = n by omega, hL1, hN] at hseg
  simpa [top] using hseg

/-- **Theorem DN, lower side, at every c ∈ [r, 2)** (run 12 had it only at c = r).
BW's system with the β = 1 envelope (contains R2 and C1): a derivation of ⁰∃^{s}DTS(v) from
DTS(a) has v ≥ ν*(c)·a, ν*(c) = c − 1/(c−1), and strictly if a > 0. -/
theorem derived_ns_lower {c : ℝ} (hc : r7 ≤ c) (hc2 : c < 2) {n : ℕ} {L : ℕ → RLine}
    {a s v : ℝ} (h : DerivesFrom (Step c 1) n L a) (hN : L n = ([s], v)) :
    tau0 c * a ≤ v ∧ (0 < a → tau0 c * a < v) := by
  have hc1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  have hβ : 1 / (r7 * (r7 - 1)) ≤ (1 : ℝ) := by
    rw [div_le_one (by nlinarith [one_le_r7r7m1])]; exact one_le_r7r7m1
  have hnn := (derives_restrict hc hβ h).2
  have ha : 0 ≤ a := h.2.2.1
  have htau1 : tau0 c < 1 := by
    unfold tau0
    have : 1 < 1 / (c - 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
    linarith
  rcases derived_concl hc1 hc2.le h hnn hN with ⟨-, hd⟩ | ⟨μ, ν, hA, -, hd⟩
  · refine ⟨by nlinarith, fun hpos => by nlinarith⟩
  · have hI := ach_inv_one hc hc2 hA
    have hν : tau0 c < ν := hI.2.2.2
    refine ⟨by nlinarith, fun hpos => by nlinarith⟩

/-- Single use of the derived NS: c·ν*(c) ≥ 1 for c ≥ r, so ⁰∃^{s}DTS(v) ⊢ DTS(c·max(s,v))
never returns below a (re-derived here from `derived_ns_lower`, independently of `derived_ns`). -/
theorem derived_ns_single_use {c : ℝ} (hc : r7 ≤ c) (hc2 : c < 2) {n : ℕ} {L : ℕ → RLine}
    {a s v : ℝ} (h : DerivesFrom (Step c 1) n L a) (hN : L n = ([s], v)) : a ≤ c * max s v := by
  have h1 := (derived_ns_lower hc hc2 h hN).1
  have h2 := tau0_ge_inv hc
  have hc0 : 0 < c := by linarith [one_lt_r7]
  have ha : 0 ≤ a := h.2.2.1
  have h3 : a ≤ c * (tau0 c * a) := by
    have := mul_le_mul_of_nonneg_right h2 ha
    rw [one_div] at this
    have h4 : a = c * (c⁻¹ * a) := by field_simp
    nlinarith
  nlinarith [le_max_right s v]

/-- Non-strict refutations (W13 Lemma 4.3, case a' = a): at least one quantified line,
final exponent ≤ initial, initial > 0. -/
def RefutesNS (R : RLine → RLine → Prop) (n : ℕ) (L : ℕ → RLine) : Prop :=
  2 ≤ n ∧ (L 0).1 = [] ∧ (L n).1 = [] ∧ 0 < (L 0).2 ∧ (L n).2 ≤ (L 0).2 ∧
    (∀ i < n, R (L i) (L (i + 1))) ∧ (∀ i, 0 < i → i < n → (L i).1 ≠ [])

/-- Strict derived NS at c = r for every β ≥ β*: a derivation of ⁰∃^{s}DTS(v) from DTS(a),
a > 0, has a < r·v. -/
theorem derived_strict_r7 {β : ℝ} (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hβ1 : β ≤ 1) {n : ℕ}
    {L : ℕ → RLine} {a s v : ℝ} (h : DerivesFrom (Step r7 β) n L a)
    (hnn : ∀ i, i ≤ n → 0 ≤ (L i).2) (hN : L n = ([s], v)) (hpos : 0 < a) : a < r7 * v := by
  have hL1 := first_is_init h
  obtain ⟨hn, h0, ha, hs, hne⟩ := h
  have hseg := segment hβ hβ1 L (n - 1) 1 0 (fun i h1 h2 => hs i (by omega))
    (fun i h1 h2 => ⟨by
      have := hne i (by omega) (by omega)
      exact Nat.one_le_iff_ne_zero.mpr (fun h => this (List.length_eq_zero_iff.mp h)),
      hnn i (by omega)⟩)
    (by rw [hL1]; rfl) (by rw [show 1 + (n - 1) = n by omega, hN]; rfl)
  rw [show 1 + (n - 1) = n by omega, hL1, hN] at hseg
  have h1 := one_lt_r7
  rcases hseg with ⟨-, hd⟩ | ⟨μ, ν, hA, -, hd⟩
  · simp only at hd; nlinarith
  · simp only at hd
    have hν := (ach_inv hβ hβ1 hA).2.2.2
    have hτ := tau0_ge_inv (le_refl r7)
    have hrν : 1 < r7 * ν := by
      have h7 : 0 < r7 := by linarith
      have := mul_lt_mul_of_pos_left (lt_of_le_of_lt hτ hν) h7
      rwa [mul_one_div_cancel h7.ne'] at this
    nlinarith

/-- **No non-strict refutation** in `Step c β` for c ≥ r and β ≥ β*: the a' = a case of W13
Lemma 4.3 is excluded as well (for a > 0; W13 scale has a ≥ 1). -/
theorem no_refutation_nonstrict {c β : ℝ} (hc : r7 ≤ c) (hβ : 1 / (r7 * (r7 - 1)) ≤ β)
    (n : ℕ) (L : ℕ → RLine) : ¬ RefutesNS (Step c β) n L := by
  rintro ⟨hn, h0, hN, hpos, hle, hstep, hmid⟩
  have h1 := one_lt_r7
  have hc0 : 0 < c := by linarith
  have hsN := hstep (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at hsN
  have hmidN := hmid (n - 1) (by omega) (by omega)
  have hD : DerivesFrom (Step c β) (n - 1) L (L 0).2 := by
    refine ⟨by omega, ?_, hpos.le, fun i hi => hstep i (by omega),
      fun i h1 h2 => hmid i h1 (by omega)⟩
    rw [← h0]
  obtain ⟨hD', hnn⟩ := derives_restrict hc hβ hD
  have hβ1 : 1 / (r7 * (r7 - 1)) ≤ min β 1 :=
    le_min hβ (by rw [div_le_one (by nlinarith [one_le_r7r7m1])]; exact one_le_r7r7m1)
  rcases step_inv hsN with ⟨g1, -, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, -, g1⟩ |
    ⟨y, g0, hu1, -⟩ | ⟨g1, -, -⟩
  · exact hmidN g1
  · rw [hN] at g1; simp at g1
  · have hlen : (L (n - 1)).1 = [y] := by rw [g0, hN]; rfl
    have hLn1 : L (n - 1) = ([y], (L (n - 1)).2) := by
      rw [← hlen]
    have hs := derived_strict_r7 hβ1 (min_le_right _ _) hD' hnn hLn1 hpos
    have he : c * (L (n - 1)).2 ≤ (L n).2 :=
      le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hc0.le) hu1
    have hv0 := hnn (n - 1) le_rfl
    have : r7 * (L (n - 1)).2 ≤ c * (L (n - 1)).2 := mul_le_mul_of_nonneg_right hc hv0
    linarith
  · rw [hN] at g1; simp at g1; exact hmidN (List.length_eq_zero_iff.mp g1.symm)

/-- Non-strict refutations in LStepX. -/
def LRefutesXNS (c β : ℝ) (n : ℕ) (L : ℕ → LLine) : Prop :=
  2 ≤ n ∧ (L 0).1 = [] ∧ (L n).1 = [] ∧ 0 < (L 0).2.1 ∧ 0 ≤ (L 0).2.2 ∧
    (L n).2.1 ≤ (L 0).2.1 ∧ (∀ i < n, LStepX c β (L i) (L (i + 1))) ∧
    (∀ i, 0 < i → i < n → (L i).1 ≠ [])

/-- **No non-strict refutation in LStepX (β = 1) for c > r.** The inner part is run at c = r
(`lstepX_restrict`, `lsegmentX`), the final slowdown at c. -/
theorem no_refutation_locX_nonstrict {c : ℝ} (hc : r7 < c) (n : ℕ) (L : ℕ → LLine) :
    ¬ LRefutesXNS c 1 n L := by
  rintro ⟨hn, h0, hN, ha, hl, hle, hstep, hmid⟩
  have h95 := nine_fifths_lt_r7
  have hr2 := r7_lt_two
  have hc0 : (0 : ℝ) < c := by linarith
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).2.1 ∧ 0 ≤ (L i).2.2 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨ha.le, hl⟩
    | succ i ih =>
      intro hi
      obtain ⟨a1, a2⟩ := ih (by omega)
      exact lstepX_nonneg hc0.le (hstep i (by omega)) a1 a2
  have hstepR : ∀ i < n, LStepX r7 1 (L i) (L (i + 1)) :=
    fun i hi => lstepX_restrict zero_le_one hc.le (hstep i hi) (hnn i hi.le).1
  rcases lstepX_inv (hstep 0 (by omega)) with ⟨-, h1, h2⟩ |
    ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, e0, -⟩ | ⟨b, xc, lc, e0, -⟩ | ⟨hl0, -, -, ha', -⟩
  · have hsN := hstep (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at hsN
    have hmidN := hmid (n - 1) (by omega) (by omega)
    rcases lstepX_inv hsN with ⟨g1, -, -⟩ |
      ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, -, g1⟩ | ⟨y, xc, lc, g0, hu1₀, -⟩ | ⟨g1, -⟩
    · exact hmidN g1
    · rw [hN] at g1; simp at g1
    · have hu1 : c * max y (L (n - 1)).2.1 ≤ (L n).2.1 :=
        le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hc0.le) hu1₀
      have hlen1 : (L (n - 1)).1.length = 0 + 1 := by rw [g0, hN]; rfl
      have hseg := lsegmentX h95.le hr2.le zero_le_one le_rfl (by rw [cub_r7]; norm_num) L
        (n - 2) 1 0
        (fun i h1 h2 => hstepR i (by omega))
        (fun i h1 h2 => ⟨by
          have := hmid i (by omega) (by omega)
          exact Nat.one_le_iff_ne_zero.mpr (fun h => this (List.length_eq_zero_iff.mp h)),
          (hnn i (by omega)).1, (hnn i (by omega)).2⟩)
        (by rw [h1]; rfl) (by rw [show 1 + (n - 2) = n - 1 by omega]; exact hlen1)
      rw [show 1 + (n - 2) = n - 1 by omega, h1, h2] at hseg
      have hy : ltop (L (n - 1)).1 = y := by rw [g0, ltop_app]
      rw [hy] at hseg
      have hr0 : (0 : ℝ) < r7 := by linarith
      have htop : (L 0).2.1 / r7 ≤ PsiB r7 1 (ltop [(0, 0, 0)]) (L 0).2.1 (L 0).2.2 := by
        have : ltop [((0 : ℝ), (0 : ℝ), (0 : ℝ))] = 0 := by
          unfold ltop lsup; simp
        rw [this]; exact psiB_top (by linarith) ha.le hl
      have hmax := le_trans htop hseg
      have h3 : r7 * ((L 0).2.1 / r7) ≤ r7 * max y (L (n - 1)).2.1 :=
        mul_le_mul_of_nonneg_left hmax hr0.le
      rw [mul_div_cancel₀ _ hr0.ne'] at h3
      have hm0 : 0 ≤ max y (L (n - 1)).2.1 :=
        le_trans (hnn (n - 1) (by omega)).1 (le_max_right _ _)
      have h4 : r7 * max y (L (n - 1)).2.1 < c * max y (L (n - 1)).2.1 := by
        rcases hm0.lt_or_eq with hm | hm
        · exact mul_lt_mul_of_pos_right hc hm
        · rw [← hm] at h3; linarith
      linarith
    · rw [hN] at g1; simp at g1; exact hmidN (List.length_eq_zero_iff.mp g1.symm)
  · rw [h0] at e0; simp at e0
  · rw [h0] at e0; simp at e0
  · exact hmid 1 (by omega) (by omega) (List.length_eq_zero_iff.mp (by rw [hl0, h0]; rfl))

/-- Non-vacuity of `RefutesNS`: the Lipton–Viglas refutation at c = 7/5 < r is one. -/
theorem lv_refutesNS : RefutesNS (Step (7 / 5) 1) 4 lvLines := by
  obtain ⟨-, h0, hN, -, hlt, hs, hne⟩ := lv_refutation
  refine ⟨by norm_num, h0, hN, by simp [lvLines], hlt.le, fun i hi => ?_, hne⟩
  refine stepS_step (S := fun B M => (7 / 5 : ℝ) * max B M)
    (fun B M => by nlinarith [le_max_right B M])
    (fun B M => by nlinarith [le_max_left B M, le_max_right B M]) (hs i hi)

end AU
end PastaMath.SatBarriers
