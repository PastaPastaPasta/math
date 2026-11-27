-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Protocol

/-!
The calculus used to derive inclusions, then fed back as rules.

* `Der R`: rules defined inductively as finite compositions of `R`-steps through quantified
  lines, with any nesting (`der_der`). Refutations in `Der (Step c β)` expand to `Step`
  refutations, so `no_refutation_der` covers every bootstrapped proof of finite length.
* `step_scale`, `der_scale`: the reduced system is invariant under scaling all exponents,
  so a derived rule may be used at every scale.
* `zero_segment`: a segment whose top superscript starts and ends at 0 never lowers the kernel.
* `derived_kappa`: for c ≥ r, a derivation of 0 E^{s₁} A^{s₂} DTS(v) from DTS(a) with s₂ ≤ 0
  (the universal block passes only the input) has s₁ + v ≥ a: no derived κ < 1 speedup.
* `derived_ns`: for c ≥ r, a derivation of 0 E^{s} DTS(v) from DTS(a) has a ≤ c·max(s, v).
-/

namespace PastaMath.SatBarriers
namespace BS

open PR

inductive Der (R : RLine → RLine → Prop) : RLine → RLine → Prop
  | single {L L' : RLine} : R L L' → Der R L L'
  | trans {L M L' : RLine} : Der R L M → M.1 ≠ [] → Der R M L' → Der R L L'

theorem der_path {R : RLine → RLine → Prop} {L L' : RLine} (h : Der R L L') :
    PathStep R L L' := by
  induction h with
  | single h => exact path_single h
  | trans _ hM _ ih1 ih2 => exact path_trans ih1 hM ih2

theorem der_der {R : RLine → RLine → Prop} {L L' : RLine} (h : Der (Der R) L L') :
    Der R L L' := by
  induction h with
  | single h => exact h
  | trans _ hM _ ih1 ih2 => exact Der.trans ih1 hM ih2

theorem refutes_expand_der {R : RLine → RLine → Prop} {n : ℕ} {L : ℕ → RLine}
    (h : RefutesWith (Der R) n L) : ∃ (n' : ℕ) (g : ℕ → RLine), RefutesWith R n' g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact refutes_expand_path ⟨h1, h2, h3, h4, h5, fun i hi => der_path (h6 i hi), h7⟩

theorem no_refutation_der {c β : ℝ} (hc : r7 ≤ c) (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (n : ℕ)
    (L : ℕ → RLine) : ¬ RefutesWith (Der (Step c β)) n L := by
  intro h
  obtain ⟨n', g, hg⟩ := refutes_expand_der h
  exact no_refutation hc hβ n' g hg

def scale (l : ℝ) (L : RLine) : RLine := (L.1.map (l * ·), l * L.2)

theorem getD_map_mul (l : ℝ) (bs : List ℝ) (i : ℕ) :
    (bs.map (l * ·)).getD i 0 = l * bs.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bs[i]? <;> simp

theorem top_map_mul (l : ℝ) (bs : List ℝ) : top (bs.map (l * ·)) = l * top bs := by
  unfold top
  rw [List.length_map, getD_map_mul]

theorem step_scale {c β l : ℝ} (hl : 0 < l) {L L' : RLine} (h : Step c β L L') :
    Step c β (scale l L) (scale l L') := by
  cases h with
  | init a => simpa [scale] using Step.init (c := c) (β := β) (l * a)
  | speed bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    have e1 : scale l (bs ++ [b], a) = (bs.map (l * ·) ++ [l * b], l * a) := by simp [scale]
    have e2 : scale l (bs ++ [b₁, b₂], a₂) = (bs.map (l * ·) ++ [l * b₁, l * b₂], l * a₂) := by
      simp [scale]
    rw [e1, e2]
    refine Step.speed _ _ _ (l * x) _ _ _ (by positivity) (mul_le_mul_of_nonneg_left hxa hl.le)
      ?_ (mul_le_mul_of_nonneg_left h₂ hl.le) ?_
    · rw [← mul_max_of_nonneg _ _ hl.le]; exact mul_le_mul_of_nonneg_left h₁ hl.le
    · have := mul_le_mul_of_nonneg_left h₃ hl.le; linarith
  | slow bs b a e h₁ h₂ =>
    have e1 : scale l (bs ++ [b], a) = (bs.map (l * ·) ++ [l * b], l * a) := by simp [scale]
    have e2 : scale l (bs, e) = (bs.map (l * ·), l * e) := rfl
    rw [e1, e2]
    apply Step.slow
    · rw [← mul_max_of_nonneg _ _ hl.le]
      have := mul_le_mul_of_nonneg_left h₁ hl.le; linarith
    · rw [top_map_mul, ← mul_max_of_nonneg _ _ hl.le]
      have := mul_le_mul_of_nonneg_left h₂ hl.le; linarith
  | weak bs bs' a a' hlen hle ha =>
    apply Step.weak
    · simp [hlen]
    · intro i; rw [getD_map_mul, getD_map_mul]; exact mul_le_mul_of_nonneg_left (hle i) hl.le
    · exact mul_le_mul_of_nonneg_left ha hl.le

theorem der_scale {c β l : ℝ} (hl : 0 < l) {L L' : RLine} (h : Der (Step c β) L L') :
    Der (Step c β) (scale l L) (scale l L') := by
  induction h with
  | single h => exact Der.single (step_scale hl h)
  | trans _ hM _ ih1 ih2 =>
    refine Der.trans ih1 ?_ ih2
    simpa [scale] using hM

theorem step_getD_mono1 {c β : ℝ} {L L' : RLine} (h : Step c β L L') {k : ℕ}
    (hk : k + 1 ≤ L.1.length) (hk' : k + 1 ≤ L'.1.length) :
    L.1.getD k 0 ≤ L'.1.getD k 0 := by
  rcases step_inv h with ⟨h1, -, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, hb₁, -, -, h1, h2⟩ |
    ⟨b, h1, -, -⟩ | ⟨-, hle, -⟩
  · rw [h1] at hk; simp at hk
  · rw [h1, h2]
    rw [h1] at hk
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k bs.length with hlt | hge
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
    · have hkb : k = bs.length := by omega
      subst hkb
      rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl,
        Nat.sub_self]
      exact le_trans (le_max_right _ _) hb₁
  · rw [h1]
    rw [List.getD_append _ _ _ _ (by omega)]
  · exact hle k

theorem seg_getD_mono {c β : ℝ} (L : ℕ → RLine) (k p : ℕ) :
    ∀ len : ℕ, (∀ i, p ≤ i → i < p + len → Step c β (L i) (L (i + 1))) →
      (∀ i, p ≤ i → i ≤ p + len → k + 1 ≤ (L i).1.length) →
      (L p).1.getD k 0 ≤ (L (p + len)).1.getD k 0 := by
  intro len
  induction len with
  | zero => intro _ _; exact le_rfl
  | succ len ih =>
    intro hs hd
    have h1 := ih (fun i h1 h2 => hs i h1 (by omega)) (fun i h1 h2 => hd i h1 (by omega))
    have h2 := step_getD_mono1 (hs (p + len) (by omega) (by omega)) (hd (p + len) (by omega)
      (by omega)) (hd (p + len + 1) (by omega) (by omega))
    rw [show p + (len + 1) = p + len + 1 by omega]
    exact le_trans h1 h2

theorem zero_segment {β : ℝ} (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hβ1 : β ≤ 1) (L : ℕ → RLine) :
    ∀ len p k : ℕ, (∀ i, p ≤ i → i < p + len → Step r7 β (L i) (L (i + 1))) →
      (∀ i, p ≤ i → i ≤ p + len → k + 1 ≤ (L i).1.length ∧ 0 ≤ (L i).2) →
      (L p).1.length = k + 1 → (L (p + len)).1.length = k + 1 →
      0 ≤ top (L p).1 → top (L (p + len)).1 ≤ 0 → (L p).2 ≤ (L (p + len)).2 := by
  have hc1 := one_lt_r7
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
  intro p k hstep hdep hp hq htp htq
  rcases Nat.eq_zero_or_pos len with h0 | hlen
  · subst h0; exact le_rfl
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
      ⟨y, f0, hu1, -⟩ | ⟨f0, -, -⟩
    · rw [h1] at hlA; simp at hlA
    · rw [f1] at hm3; rw [f0] at hlA
      simp only [List.length_append, List.length_cons, List.length_nil] at hm3 hlA
      omega
    · -- index k is monotone from p+1 to the end
      have hX1 : (L (p + 1)).1.getD k 0 = b₁ := by
        rw [e1, List.getD_append_right _ _ _ _ (by omega), hbs, Nat.sub_self]; rfl
      have hmonoAll := seg_getD_mono L k (p + 1) (p + len - (p + 1))
        (fun i h1 h2 => hstep i (by omega) (by omega))
        (fun i h1 h2 => (hdep i (by omega) (by omega)).1)
      rw [show p + 1 + (p + len - (p + 1)) = p + len by omega, hX1, ← top_eq_getD hq] at hmonoAll
      have hx0 : x = 0 := by
        have := le_trans (le_max_left x b) h₁
        linarith
      have hmonoM := seg_getD_mono L k (p + 1) (m0 - (p + 1))
        (fun i h1 h2 => hstep i (by omega) (by omega))
        (fun i h1 h2 => (hdep i (by omega) (by omega)).1)
      rw [show p + 1 + (m0 - (p + 1)) = m0 by omega, hX1, ← top_eq_getD hm3] at hmonoM
      have htm0 : 0 ≤ top (L m0).1 := by
        have := le_trans (le_max_left x b) h₁
        linarith
      have hA := segment hβ hβ1 L (m0 - 1 - (p + 1)) (p + 1) (k + 1)
        (fun i h1 h2 => hstep i (by omega) (by omega))
        (fun i h1 h2 => ⟨hmin i h1 (by omega), (hdep i (by omega) (by omega)).2⟩) hl1 (by
          rw [show p + 1 + (m0 - 1 - (p + 1)) = m0 - 1 by omega]; exact hlA)
      rw [show p + 1 + (m0 - 1 - (p + 1)) = m0 - 1 by omega] at hA
      have hB := ih (p + len - m0) (by omega) m0 k
        (fun i h1 h2 => hstep i (by omega) (by omega))
        (fun i h1 h2 => hdep i (by omega) (by omega)) hm3 (by
          rw [show m0 + (p + len - m0) = p + len by omega]; exact hq) htm0 (by
          rw [show m0 + (p + len - m0) = p + len by omega]; exact htq)
      rw [show m0 + (p + len - m0) = p + len by omega] at hB
      have hd1 : (L p).2 ≤ (L (p + 1)).2 := by rw [hx0] at h₃; linarith
      have hz0 : 0 ≤ (L (m0 - 1)).2 := (hdep (m0 - 1) (by omega) (by omega)).2
      have hd10 : 0 ≤ (L (p + 1)).2 := (hdep (p + 1) (by omega) (by omega)).2
      have hu : r7 * (L (m0 - 1)).2 ≤ (L m0).2 := by
        have := mul_le_mul_of_nonneg_left (le_max_right y (L (m0 - 1)).2)
          (by linarith : (0 : ℝ) ≤ r7)
        linarith
      have hmid : (L (p + 1)).2 ≤ (L m0).2 := by
        rcases hA with ⟨-, hd⟩ | ⟨μ, ν, hAch, -, hd⟩
        · nlinarith
        · have hν := (ach_inv hβ hβ1 hAch).2.2.2
          have hτ := tau0_ge_inv (le_refl r7)
          have hrν : 1 < r7 * ν := by
            have h7 : 0 < r7 := by linarith
            have := mul_lt_mul_of_pos_left (lt_of_le_of_lt hτ hν) h7
            rwa [mul_one_div_cancel h7.ne'] at this
          nlinarith
      linarith
    · rw [f0] at hm3; omega
  · have := (hdep (p + 1) (by omega) (by omega)).1
    rw [e0] at hp
    simp only [List.length_append, List.length_singleton] at hp this
    omega
  · have hl1 : (L (p + 1)).1.length = k + 1 := by rw [hl, hp]
    have htop : top (L p).1 ≤ top (L (p + 1)).1 := by
      rw [top_eq_getD hp, top_eq_getD hl1]; exact hle k
    have hrest := ih (len - 1) (by omega) (p + 1) k
      (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => hdep i (by omega) (by omega)) hl1 (by
        rw [show p + 1 + (len - 1) = p + len by omega]; exact hq) (le_trans htp htop) (by
        rw [show p + 1 + (len - 1) = p + len by omega]; exact htq)
    rw [show p + 1 + (len - 1) = p + len by omega] at hrest
    linarith

/-- A derivation from DTS(a) through quantified lines to 0 E^{s₁} A^{s₂} DTS(v). -/
def DerivesFrom (R : RLine → RLine → Prop) (n : ℕ) (L : ℕ → RLine) (a : ℝ) : Prop :=
  1 ≤ n ∧ L 0 = ([], a) ∧ 0 ≤ a ∧ (∀ i < n, R (L i) (L (i + 1))) ∧
    (∀ i, 0 < i → i ≤ n → (L i).1 ≠ [])

theorem derives_restrict {c β : ℝ} (hc : r7 ≤ c) (hβ : 1 / (r7 * (r7 - 1)) ≤ β) {n : ℕ}
    {L : ℕ → RLine} {a : ℝ} (h : DerivesFrom (Step c β) n L a) :
    DerivesFrom (Step r7 (min β 1)) n L a ∧ ∀ i, i ≤ n → 0 ≤ (L i).2 := by
  obtain ⟨hn, h0, ha, hs, hne⟩ := h
  have h1 := one_lt_r7
  have hβ0 : 0 ≤ min β 1 := le_min (le_trans (by positivity) hβ) zero_le_one
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).2 := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ha
    | succ i ih => intro hi; exact step_nonneg (by linarith) (hs i (by omega)) (ih (by omega))
  exact ⟨⟨hn, h0, ha, fun i hi => step_restrict hc h1.le hβ0 (min_le_left _ _) (hs i hi)
    (hnn i hi.le), hne⟩, hnn⟩

theorem first_is_init {c β : ℝ} {n : ℕ} {L : ℕ → RLine} {a : ℝ}
    (h : DerivesFrom (Step c β) n L a) : L 1 = ([0], a) := by
  obtain ⟨hn, h0, -, hs, hne⟩ := h
  have hs0 := hs 0 (by omega)
  rw [h0] at hs0
  rcases step_inv hs0 with ⟨-, h2, h3⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -⟩ |
    ⟨b, e0, -, -⟩ | ⟨hl, -, -⟩
  · exact Prod.ext h2 h3
  · simp at e0
  · simp at e0
  · exact absurd (List.length_eq_zero_iff.mp (by rw [hl]; rfl)) (hne 1 (by omega) hn)

theorem derived_kappa {c β : ℝ} (hc : r7 ≤ c) (hβ : 1 / (r7 * (r7 - 1)) ≤ β) {n : ℕ}
    {L : ℕ → RLine} {a s₁ s₂ v : ℝ} (h : DerivesFrom (Step c β) n L a)
    (hN : L n = ([s₁, s₂], v)) (hs₂ : s₂ ≤ 0) : a ≤ s₁ + v := by
  have hL1 := first_is_init h
  obtain ⟨⟨hn, h0, ha, hs, hne⟩, hnn⟩ := derives_restrict hc hβ h
  have hβ' : 1 / (r7 * (r7 - 1)) ≤ min β 1 := le_min hβ (by
    rw [div_le_one (by linarith [one_le_r7r7m1, one_lt_r7])]; exact one_le_r7r7m1)
  have hβ1' : min β 1 ≤ 1 := min_le_right _ _
  have hlenN : (L n).1.length = 2 := by rw [hN]; rfl
  have hn2 : 2 ≤ n := by
    by_contra hcon
    have : n = 1 := by omega
    rw [this, hL1] at hlenN; simp at hlenN
  classical
  set P : ℕ → Prop := fun i => (L i).1.length = 1 with hP
  have hP1 : P 1 := by simp only [hP, hL1]; rfl
  set m := Nat.findGreatest P n with hm
  have hPm : P m := Nat.findGreatest_spec (P := P) (m := 1) (by omega) hP1
  have hm1 : 1 ≤ m := Nat.le_findGreatest (P := P) (by omega) hP1
  have hmn : m ≤ n := Nat.findGreatest_le n
  have hmn' : m < n := by
    rcases Nat.lt_or_ge m n with h' | h'
    · exact h'
    · have : m = n := by omega
      rw [this] at hPm; simp only [hP, hlenN] at hPm; omega
  have hafter : ∀ i, m < i → i ≤ n → 2 ≤ (L i).1.length := by
    intro i hi1 hi2
    have hnot : ¬ P i := Nat.findGreatest_is_greatest (P := P) hi1 hi2
    have hne' := hne i (by omega) hi2
    have : (L i).1.length ≠ 0 := fun h0 => hne' (List.length_eq_zero_iff.mp h0)
    simp only [hP] at hnot
    omega
  have hbefore : ∀ i, 1 ≤ i → i ≤ n → 1 ≤ (L i).1.length := by
    intro i hi1 hi2
    have hne' := hne i (by omega) hi2
    have : (L i).1.length ≠ 0 := fun h0 => hne' (List.length_eq_zero_iff.mp h0)
    omega
  have hsm := hs m hmn'
  have hlm1 : (L (m + 1)).1.length = 2 := by
    have h1 := hafter (m + 1) (by omega) (by omega)
    have h2 := (step_len hsm).1
    simp only [hP] at hPm
    omega
  rcases step_inv hsm with ⟨g1, -, -⟩ | ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, e0, e1⟩ |
    ⟨y, g0, -, -⟩ | ⟨g0, -, -⟩
  · simp only [hP] at hPm; rw [g1] at hPm; simp at hPm
  · have hbs : bs = [] := by
      have : (L m).1.length = 1 := hPm
      rw [e0] at this; simp only [List.length_append, List.length_singleton] at this
      exact List.length_eq_zero_iff.mp (by omega)
    subst hbs
    simp only [List.nil_append] at e0 e1
    -- depth-2 segment from m+1 to n, index 1 monotone, index 0 monotone
    have hseg2 := zero_segment hβ' hβ1' L (n - (m + 1)) (m + 1) 1
      (fun i h1 h2 => hs i (by omega))
      (fun i h1 h2 => ⟨hafter i (by omega) (by omega), hnn i (by omega)⟩) hlm1 (by
        rw [show m + 1 + (n - (m + 1)) = n by omega]; exact hlenN)
    have hmono1 := seg_getD_mono L 1 (m + 1) (n - (m + 1))
      (fun i h1 h2 => hs i (by omega)) (fun i h1 h2 => hafter i (by omega) (by omega))
    have hmono0 := seg_getD_mono L 0 (m + 1) (n - (m + 1))
      (fun i h1 h2 => hs i (by omega))
      (fun i h1 h2 => le_trans (by omega) (hafter i (by omega) (by omega)))
    rw [show m + 1 + (n - (m + 1)) = n by omega, hN, e1] at hmono1 hmono0
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hmono1 hmono0
    have hmono00 := seg_getD_mono L 0 1 (m - 1)
      (fun i h1 h2 => hs i (by omega)) (fun i h1 h2 => hbefore i h1 (by omega))
    rw [show 1 + (m - 1) = m by omega, hL1, e0] at hmono00
    simp only [List.getD_cons_zero] at hmono00
    have htopm : top (L (m + 1)).1 = b₂ := by rw [e1]; rfl
    have htopn : top (L n).1 = s₂ := by rw [hN]; rfl
    have hb₂0 : 0 ≤ b₂ := le_trans hmono00 h₂
    rw [htopm, show m + 1 + (n - (m + 1)) = n by omega, htopn] at hseg2
    have hv : (L (m + 1)).2 ≤ v := by
      have := hseg2 hb₂0 hs₂
      rw [hN] at this; exact this
    -- depth-1 segment from 1 to m
    have hseg1 := zero_segment hβ' hβ1' L (m - 1) 1 0
      (fun i h1 h2 => hs i (by omega))
      (fun i h1 h2 => ⟨hbefore i h1 (by omega), hnn i (by omega)⟩) (by rw [hL1]; rfl) (by
        rw [show 1 + (m - 1) = m by omega]; exact hPm)
    rw [show 1 + (m - 1) = m by omega, hL1] at hseg1
    have htop1 : top ([0] : List ℝ) = 0 := rfl
    have htm : top (L m).1 = b := by rw [e0]; rfl
    rw [htop1, htm] at hseg1
    have hd : a ≤ (L m).2 := by
      have := hseg1 le_rfl (by linarith)
      simpa using this
    have hs1 : x ≤ s₁ := le_trans (le_max_left _ _) (le_trans h₁ hmono0)
    linarith
  · simp only [hP] at hPm; rw [g0] at hPm
    simp only [List.length_append, List.length_singleton] at hPm
    have := hafter (m + 1) (by omega) (by omega)
    omega
  · simp only [hP] at hPm
    have := hafter (m + 1) (by omega) (by omega)
    omega

theorem derived_ns {c β : ℝ} (hc : r7 ≤ c) (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hβ1 : β ≤ 1)
    {n : ℕ} {L : ℕ → RLine} {a s v : ℝ} (h : DerivesFrom (Step c β) n L a)
    (hN : L n = ([s], v)) : a ≤ c * max s v := by
  have hvn : 0 ≤ v := by
    have := (derives_restrict hc hβ h).2 n le_rfl
    rw [hN] at this; exact this
  by_contra hlt
  push Not at hlt
  obtain ⟨hn, h0, ha, hs, hne⟩ := h
  have hc1 : 1 < c := lt_of_lt_of_le one_lt_r7 hc
  let g : ℕ → RLine := fun i => if i ≤ n then L i else ([], c * max s v)
  have hg : RefutesWith (Step c β) (n + 1) g := by
    refine ⟨by omega, by simp [g, h0], by simp [g], by simp [g, h0, ha], ?_, ?_, ?_⟩
    · simp only [g, show ¬ (n + 1 ≤ n) by omega, if_false]
      rw [h0]; exact hlt
    · intro i hi
      by_cases hin : i < n
      · simp only [g, show i ≤ n by omega, show i + 1 ≤ n by omega, if_true]
        exact hs i hin
      · have : i = n := by omega
        subst this
        simp only [g, le_refl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false, hN]
        have hβ0 : 0 ≤ β := le_trans (le_of_lt (div_pos one_pos (by
          nlinarith [one_le_r7r7m1]))) hβ
        apply Step.slow [] s v
        · exact le_rfl
        · have hm : 0 ≤ max s v := le_trans hvn (le_max_right _ _)
          have : β * (c - 1) ≤ c := by nlinarith
          have := mul_le_mul_of_nonneg_right this hm
          simp only [top, List.length_nil, List.getD_nil]
          linarith
    · intro i hi1 hi2
      simp only [g, show i ≤ n by omega, if_true]
      exact hne i hi1 (by omega)
  exact no_refutation hc hβ (n + 1) g hg

/-- Sharpness of `derived_kappa` in its hypothesis s₂ ≤ 0: at c = 181/100 > r a four-step
derivation reaches 0 E^0 A^{1/2} DTS(181/200), so s₁ + v < a once the universal block passes
more than the input (the dual Lipton–Viglas step). -/
noncomputable def kLines : ℕ → RLine
  | 0 => ([], 1)
  | 1 => ([0], 1)
  | 2 => ([0, 0], 1)
  | 3 => ([0, 1 / 2, 0], 1 / 2)
  | _ => ([0, 1 / 2], 181 / 200)

theorem r7_lt_181_100' : r7 < 181 / 100 := by
  have hpos : 0 < cub (181 / 100) := by unfold cub; norm_num
  rcases lt_or_ge r7 (181 / 100) with h | h
  · exact h
  · exfalso
    rcases eq_or_lt_of_le h with h' | h'
    · have := (cub_eq_zero_iff (by norm_num : (1 : ℝ) ≤ 181 / 100)).mpr h'
      linarith
    · have := (cub_neg_iff (by norm_num : (1 : ℝ) ≤ 181 / 100)).mpr h'
      linarith

theorem derived_kappa_sharp :
    DerivesFrom (Step (181 / 100) 1) 4 kLines 1 ∧ kLines 4 = ([0, 1 / 2], 181 / 200) ∧
      (0 : ℝ) + 181 / 200 < 1 ∧ r7 < 181 / 100 := by
  refine ⟨⟨by norm_num, rfl, by norm_num, ?_, ?_⟩, rfl, by norm_num, r7_lt_181_100'⟩
  · intro i hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    · exact Step.init 1
    · have h := Step.speed (c := 181 / 100) (β := 1) [] 0 1 0 0 0 1 le_rfl (by norm_num)
        (by norm_num) le_rfl (by norm_num)
      simpa [kLines] using h
    · have h := Step.speed (c := 181 / 100) (β := 1) [0] 0 1 (1 / 2) (1 / 2) 0 (1 / 2)
        (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
      simpa [kLines] using h
    · have h := Step.slow (c := 181 / 100) (β := 1) [0, 1 / 2] 0 (1 / 2) (181 / 200)
        (by norm_num) (by simp [top]; norm_num)
      simpa [kLines] using h
  · intro i hi1 hi2
    obtain rfl | rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    all_goals simp [kLines]

end BS
end PastaMath.SatBarriers
