-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Derivation

namespace PastaMath.SatBarriers

structure FLine where
  bs : List ℝ
  a : ℝ
  fresh : Bool

inductive Step2 (c β₁ β₂ : ℝ) : FLine → FLine → Prop
  | init (a : ℝ) (fl : Bool) : Step2 c β₁ β₂ ⟨[], a, fl⟩ ⟨[0], a, false⟩
  | speed (bs : List ℝ) (b a x b₁ b₂ a₂ : ℝ) (fl : Bool) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₁ : max x b ≤ b₁) (h₂ : b ≤ b₂) (h₃ : a - x ≤ a₂) :
      Step2 c β₁ β₂ ⟨bs ++ [b], a, fl⟩ ⟨bs ++ [b₁, b₂], a₂, true⟩
  | slow (bs : List ℝ) (b a e : ℝ) (fl : Bool) (h₁ : c * max b a ≤ e)
      (h₂ : top bs + (if fl then β₁ else β₂) * (c - 1) * max b a ≤ e) :
      Step2 c β₁ β₂ ⟨bs ++ [b], a, fl⟩ ⟨bs, e, false⟩
  | weak (bs bs' : List ℝ) (a a' : ℝ) (fl : Bool) (hl : bs'.length = bs.length)
      (hle : ∀ i, bs.getD i 0 ≤ bs'.getD i 0) (ha : a ≤ a') :
      Step2 c β₁ β₂ ⟨bs, a, fl⟩ ⟨bs', a', fl⟩

def RefutesWith2 (R : FLine → FLine → Prop) (n : ℕ) (L : ℕ → FLine) : Prop :=
  1 ≤ n ∧ (L 0).bs = [] ∧ (L n).bs = [] ∧ 0 ≤ (L 0).a ∧ (L n).a < (L 0).a ∧
    (∀ i < n, R (L i) (L (i + 1))) ∧ (∀ i, 0 < i → i < n → (L i).bs ≠ [])

def Concl2 (c β b d b' d' : ℝ) (fl fl' : Bool) : Prop :=
  (fl' = fl ∧ b ≤ b' ∧ d ≤ d') ∨ (fl' = false ∧ ∃ μ ν, Ach c β μ ν ∧ c * μ * b ≤ d' ∧ ν * d ≤ d')

theorem step2_inv {c β₁ β₂ : ℝ} {L L' : FLine} (h : Step2 c β₁ β₂ L L') :
    (L.bs = [] ∧ L'.bs = [0] ∧ L'.a = L.a ∧ L'.fresh = false) ∨
    (∃ (bs : List ℝ) (b x b₁ b₂ : ℝ), 0 ≤ x ∧ x ≤ L.a ∧ max x b ≤ b₁ ∧ b ≤ b₂ ∧
      L.a - x ≤ L'.a ∧ L.bs = bs ++ [b] ∧ L'.bs = bs ++ [b₁, b₂] ∧ L'.fresh = true) ∨
    (∃ b : ℝ, L.bs = L'.bs ++ [b] ∧ c * max b L.a ≤ L'.a ∧
      top L'.bs + (if L.fresh then β₁ else β₂) * (c - 1) * max b L.a ≤ L'.a ∧
      L'.fresh = false) ∨
    (L'.bs.length = L.bs.length ∧ (∀ i, L.bs.getD i 0 ≤ L'.bs.getD i 0) ∧ L.a ≤ L'.a ∧
      L'.fresh = L.fresh) := by
  cases h with
  | init a fl => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | speed bs b a x b₁ b₂ a₂ fl hx hxa h₁ h₂ h₃ =>
    exact Or.inr (Or.inl ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, rfl, rfl, rfl⟩)
  | slow bs b a e fl h₁ h₂ => exact Or.inr (Or.inr (Or.inl ⟨b, rfl, h₁, h₂, rfl⟩))
  | weak bs bs' a a' fl hl hle ha => exact Or.inr (Or.inr (Or.inr ⟨hl, hle, ha, rfl⟩))

theorem step2_len {c β₁ β₂ : ℝ} {L L' : FLine} (h : Step2 c β₁ β₂ L L') :
    L'.bs.length ≤ L.bs.length + 1 ∧ L.bs.length ≤ L'.bs.length + 1 := by
  rcases step2_inv h with ⟨h1, h2, _, _⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, h1, h2, -⟩ |
    ⟨b, h1, -, -, -⟩ | ⟨h1, -, -, -⟩
  · rw [h1, h2]; simp
  · rw [h1, h2]; simp
  · rw [h1]; simp only [List.length_append, List.length_singleton]; omega
  · omega

theorem step2_getD_mono {c β₁ β₂ : ℝ} {L L' : FLine} (h : Step2 c β₁ β₂ L L') {k : ℕ}
    (hk : k + 2 ≤ L.bs.length) (hk' : k + 2 ≤ L'.bs.length) :
    L.bs.getD k 0 ≤ L'.bs.getD k 0 := by
  rcases step2_inv h with ⟨h1, -, -, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, h1, h2, -⟩ |
    ⟨b, h1, -, -, -⟩ | ⟨-, hle, -, -⟩
  · rw [h1] at hk; simp at hk
  · rw [h1] at hk ⊢
    rw [h2]
    simp only [List.length_append, List.length_singleton] at hk
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · rw [h1]
    rw [List.getD_append _ _ _ _ (by omega)]
  · exact hle k

theorem step2_nonneg {c β₁ β₂ : ℝ} (hc : 0 ≤ c) {L L' : FLine} (h : Step2 c β₁ β₂ L L')
    (hL : 0 ≤ L.a) : 0 ≤ L'.a := by
  rcases step2_inv h with ⟨-, -, h3, -⟩ | ⟨bs, b, x, b₁, b₂, -, hxa, -, -, h3, -, -, -⟩ |
    ⟨b, -, h3, -, -⟩ | ⟨-, -, h3, -⟩
  · rw [h3]; exact hL
  · linarith
  · have : 0 ≤ c * max b L.a := mul_nonneg hc (le_trans hL (le_max_right _ _))
    linarith
  · linarith

theorem step2_restrict {c β₁ β₂ c₀ γ₁ γ₂ : ℝ} (hc : c₀ ≤ c) (hc₀ : 1 ≤ c₀) (hγ₁ : 0 ≤ γ₁)
    (hγ₂ : 0 ≤ γ₂) (h₁ : γ₁ ≤ β₁) (h₂ : γ₂ ≤ β₂) {L L' : FLine} (h : Step2 c β₁ β₂ L L')
    (hL : 0 ≤ L.a) : Step2 c₀ γ₁ γ₂ L L' := by
  cases h with
  | init a fl => exact Step2.init a fl
  | speed bs b a x b₁ b₂ a₂ fl hx hxa g₁ g₂ g₃ =>
    exact Step2.speed bs b a x b₁ b₂ a₂ fl hx hxa g₁ g₂ g₃
  | weak bs bs' a a' fl hl hle ha => exact Step2.weak bs bs' a a' fl hl hle ha
  | slow bs b a e fl g₁ g₂ =>
    have hM : 0 ≤ max b a := le_trans hL (le_max_right _ _)
    apply Step2.slow bs b a e fl
    · exact le_trans (mul_le_mul_of_nonneg_right hc hM) g₁
    · have hγβ : (if fl then γ₁ else γ₂) ≤ (if fl then β₁ else β₂) := by
        cases fl <;> simp [h₁, h₂]
      have hγ0 : 0 ≤ (if fl then γ₁ else γ₂) := by cases fl <;> simp [hγ₁, hγ₂]
      have e1 : (if fl then γ₁ else γ₂) * (c₀ - 1) ≤ (if fl then β₁ else β₂) * (c - 1) :=
        mul_le_mul hγβ (by linarith) (by linarith) (le_trans hγ0 hγβ)
      have := mul_le_mul_of_nonneg_right e1 hM
      linarith

theorem refutes2_mono {R R' : FLine → FLine → Prop}
    (hR : ∀ L L', 0 ≤ L.a → R L L' → R' L L' ∧ 0 ≤ L'.a) {n : ℕ} {L : ℕ → FLine}
    (h : RefutesWith2 R n L) : RefutesWith2 R' n L := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).a := by
    intro i
    induction i with
    | zero => intro _; exact h4
    | succ i ih =>
      intro hi
      exact (hR _ _ (ih (by omega)) (h6 i (by omega))).2
  exact ⟨h1, h2, h3, h4, h5, fun i hi => (hR _ _ (hnn i hi.le) (h6 i hi)).1, h7⟩

theorem combine_imm {c β₁ β₂ : ℝ} (hc1 : 1 < c) (hβ0 : 0 ≤ β₁) (hβ1 : β₁ * (c - 1) ≤ 1)
    (hβc : (c - 1) * (1 + gam c β₁) ≤ c) (hpos : ∀ μ ν, Ach c β₂ μ ν → 1 ≤ μ ∧ 0 < ν)
    {b d x X b₂ a₂ y z u b' d' : ℝ} (hd : 0 ≤ d) (hx : 0 ≤ x)
    (hX : max x b ≤ X) (hb₂ : b ≤ b₂) (ha₂ : d - x ≤ a₂)
    (hy : b₂ ≤ y) (hz : a₂ ≤ z) (hu1 : c * max y z ≤ u)
    (hu2 : X + β₁ * (c - 1) * max y z ≤ u)
    (hB : (X ≤ b' ∧ u ≤ d') ∨ ∃ μ ν, Ach c β₂ μ ν ∧ c * μ * X ≤ d' ∧ ν * u ≤ d') :
    ∃ μ ν, Ach c β₂ μ ν ∧ c * μ * b ≤ d' ∧ ν * d ≤ d' := by
  have hc0 : 0 < c := by linarith
  have hβc0 : 0 ≤ β₁ * (c - 1) := mul_nonneg hβ0 (by linarith)
  have hxX : x ≤ X := le_trans (le_max_left _ _) hX
  have hbX : b ≤ X := le_trans (le_max_right _ _) hX
  have hm : max b (d - x) ≤ max y z := max_le_max (le_trans hb₂ hy) (le_trans ha₂ hz)
  have hcz : c * (d - x) ≤ u := by
    have := mul_le_mul_of_nonneg_left (le_trans (le_max_right b (d - x)) hm) hc0.le
    linarith
  rcases hB with ⟨_, hud⟩ | ⟨μ₁, ν₁, hA₁, hd1, hd2⟩
  · have key : max (c * max b (d - x)) (x + β₁ * (c - 1) * max b (d - x)) ≤ u := by
      apply max_le
      · exact le_trans (mul_le_mul_of_nonneg_left hm hc0.le) hu1
      · have := mul_le_mul_of_nonneg_left hm hβc0
        linarith
    obtain ⟨k1, k2⟩ := step10_bound_beta hc1 hβ0 hβ1 hd hβc key
    exact ⟨1, c - 1, Ach.base, by linarith, by linarith⟩
  · obtain ⟨hμ₁, hν₁⟩ := hpos _ _ hA₁
    rcases le_or_gt d u with hdu | hdu
    · refine ⟨μ₁, ν₁, hA₁, ?_, ?_⟩
      · have : c * μ₁ * b ≤ c * μ₁ * X := mul_le_mul_of_nonneg_left hbX (by positivity)
        linarith
      · have : ν₁ * d ≤ ν₁ * u := mul_le_mul_of_nonneg_left hdu hν₁.le
        linarith
    · have hX0 : 0 ≤ X := by linarith
      have hcX : c * X ≤ c * μ₁ * X := by
        nlinarith [mul_nonneg (mul_nonneg hc0.le hX0) (sub_nonneg.mpr hμ₁)]
      refine ⟨1, c - 1, Ach.base, ?_, ?_⟩
      · have : c * b ≤ c * X := mul_le_mul_of_nonneg_left hbX hc0.le
        linarith
      · have : c * x ≤ c * X := mul_le_mul_of_nonneg_left hxX hc0.le
        linarith

theorem combine_non {c β₂ : ℝ} (hc1 : 1 < c) (hβ0 : 0 ≤ β₂) (hβ1 : β₂ * (c - 1) ≤ 1)
    {b d x X b₂ a₂ y z u b' d' μ₂ ν₂ : ℝ} (_hx : 0 ≤ x) (hxd : x ≤ d)
    (hX : max x b ≤ X) (hb₂ : b ≤ b₂) (ha₂ : d - x ≤ a₂)
    (hA₂ : Ach c β₂ μ₂ ν₂) (hz1 : c * μ₂ * b₂ ≤ z) (hz2 : ν₂ * a₂ ≤ z)
    (hu1 : c * max y z ≤ u) (hu2 : X + β₂ * (c - 1) * max y z ≤ u)
    (hB : (X ≤ b' ∧ u ≤ d') ∨ ∃ μ ν, Ach c β₂ μ ν ∧ c * μ * X ≤ d' ∧ ν * u ≤ d') :
    ∃ μ ν, Ach c β₂ μ ν ∧ c * μ * b ≤ d' ∧ ν * d ≤ d' := by
  have hpos := fun μ ν (h : Ach c β₂ μ ν) => ach_pos hc1 hβ0 hβ1 h
  have hc0 : 0 < c := by linarith
  have hβc0 : 0 ≤ β₂ * (c - 1) := mul_nonneg hβ0 (by linarith)
  have hxX : x ≤ X := le_trans (le_max_left _ _) hX
  have hbX : b ≤ X := le_trans (le_max_right _ _) hX
  have hyz : z ≤ max y z := le_max_right _ _
  obtain ⟨hμ₂, hν₂⟩ := hpos _ _ hA₂
  have hz1' : c * μ₂ * b ≤ z := by
    have : c * μ₂ * b ≤ c * μ₂ * b₂ := mul_le_mul_of_nonneg_left hb₂ (by positivity)
    linarith
  have hz2' : ν₂ * (d - x) ≤ z := by
    have : ν₂ * (d - x) ≤ ν₂ * a₂ := mul_le_mul_of_nonneg_left ha₂ hν₂.le
    linarith
  have hcz : c * z ≤ u := le_trans (mul_le_mul_of_nonneg_left hyz hc0.le) hu1
  have hu : max (c * z) (x + β₂ * (c - 1) * z) ≤ u := by
    apply max_le hcz
    have := mul_le_mul_of_nonneg_left hyz hβc0
    linarith
  rcases hB with ⟨_, hud⟩ | ⟨μ₁, ν₁, hA₁, hd1, hd2⟩
  · rcases le_or_gt (β₂ * (c - 1) * ν₂) 1 with hβν | hβν
    · have k := btrivial_bound_beta hc1 hν₂ hβ0 hβν hz2' hu
      refine ⟨c * μ₂, c * ν₂ / (1 + gam c β₂ * ν₂), Ach.dbeta hA₂, ?_, ?_⟩
      · have : c * (c * μ₂ * b) ≤ c * z := mul_le_mul_of_nonneg_left hz1' hc0.le
        nlinarith
      · rw [div_mul_eq_mul_div]
        linarith
    · have k := btrivial_bound_beta_big hc1 hβ0 hβν hxd hz2' hu
      refine ⟨c * μ₂, 1, Ach.big (by nlinarith) le_rfl, ?_, by linarith⟩
      have : c * (c * μ₂ * b) ≤ c * z := mul_le_mul_of_nonneg_left hz1' hc0.le
      nlinarith
  · obtain ⟨hμ₁, hν₁⟩ := hpos _ _ hA₁
    refine ⟨_, _, Ach.comp hA₁ hA₂, ?_, ?_⟩
    · rcases le_total μ₁ (c * ν₁ * μ₂) with hm | hm
      · rw [max_eq_right hm]
        have e1 : c * (c * ν₁ * μ₂) * b = ν₁ * (c * (c * μ₂ * b)) := by ring
        have e2 : c * (c * μ₂ * b) ≤ c * z := mul_le_mul_of_nonneg_left hz1' hc0.le
        have e3 : ν₁ * (c * (c * μ₂ * b)) ≤ ν₁ * u :=
          mul_le_mul_of_nonneg_left (le_trans e2 hcz) hν₁.le
        linarith
      · rw [max_eq_left hm]
        have : c * μ₁ * b ≤ c * μ₁ * X := mul_le_mul_of_nonneg_left hbX (by positivity)
        linarith
    · have hden : 0 < μ₁ + ν₁ * ν₂ := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      have f1 : c * μ₁ * x ≤ d' := by
        have : c * μ₁ * x ≤ c * μ₁ * X := mul_le_mul_of_nonneg_left hxX (by positivity)
        linarith
      have f2 : c * ν₁ * ν₂ * (d - x) ≤ d' := by
        have : ν₁ * (c * (ν₂ * (d - x))) ≤ ν₁ * u := by
          apply mul_le_mul_of_nonneg_left _ hν₁.le
          have := mul_le_mul_of_nonneg_left hz2' hc0.le
          linarith
        nlinarith
      have g1 := mul_le_mul_of_nonneg_left f1 (by positivity : (0 : ℝ) ≤ ν₁ * ν₂)
      have g2 := mul_le_mul_of_nonneg_left f2 (by positivity : (0 : ℝ) ≤ μ₁)
      nlinarith

noncomputable def betaNon : ℝ := r7 * (2 - r7) / (r7 - 1)

theorem beta_non_conditions {β : ℝ} (hβ : betaNon ≤ β) (hβ1 : β ≤ 1) :
    r7 * (2 - r7) ≤ β * (r7 - 1) ∧ gam r7 β * tau0 r7 ≤ r7 - 1 ∧ 0 < gam r7 β ∧
      β * (r7 - 1) ≤ 1 ∧ 0 ≤ β := by
  have h1 := one_lt_r7
  have h2 := r7_lt_two
  have hr1 : 0 < r7 - 1 := by linarith
  have hii : r7 * (2 - r7) ≤ β * (r7 - 1) := by
    unfold betaNon at hβ
    rw [div_le_iff₀ hr1] at hβ
    exact hβ
  have hβ0 : 0 ≤ β := by
    have : 0 ≤ betaNon := by unfold betaNon; apply div_nonneg <;> nlinarith
    linarith
  refine ⟨hii, ?_, by unfold gam; nlinarith, by nlinarith, hβ0⟩
  rw [tau0_r7]
  unfold gam
  rw [show (r7 - β * (r7 - 1)) * (1 / r7) = (r7 - β * (r7 - 1)) / r7 by ring,
    div_le_iff₀ (by linarith)]
  nlinarith

theorem ach_inv2 {β : ℝ} (hβ : betaNon ≤ β) (hβ1 : β ≤ 1) {μ ν : ℝ}
    (h : Ach r7 β μ ν) : Inv r7 μ ν := by
  obtain ⟨hii, hiii, hγ, _, _⟩ := beta_non_conditions hβ hβ1
  have hc := one_lt_r7
  induction h with
  | base => exact inv_base le_rfl r7_lt_two
  | big hμ hν => exact inv_big le_rfl r7_lt_two hμ hν
  | dbeta _ ih => exact inv_dbeta le_rfl hγ hii hiii ih
  | @comp μ₁ ν₁ μ₂ ν₂ _ _ ih1 ih2 =>
    have hν1 : 0 < ν₁ := ih1.2.1
    have hpos : 0 < r7 * ν₁ := by positivity
    set μ₂' := max μ₂ (μ₁ / (r7 * ν₁)) with hμ₂'
    have h2' : Inv r7 μ₂' ν₂ := inv_weaken le_rfl ih2 (le_max_left _ _) le_rfl
    have hside : μ₁ ≤ r7 * ν₁ * μ₂' := by
      have : μ₁ = r7 * ν₁ * (μ₁ / (r7 * ν₁)) := by field_simp
      calc μ₁ = r7 * ν₁ * (μ₁ / (r7 * ν₁)) := this
        _ ≤ r7 * ν₁ * μ₂' := mul_le_mul_of_nonneg_left (le_max_right _ _) hpos.le
    have hres := inv_comp le_rfl ih1 h2' hside
    have heq : r7 * ν₁ * μ₂' = max μ₁ (r7 * ν₁ * μ₂) := by
      rw [hμ₂', mul_max_of_nonneg _ _ hpos.le, max_comm]
      congr 1
      field_simp
    rw [heq] at hres
    exact hres

theorem concl2_weak {c β b d b₀ d₀ b' d' : ℝ} {fl fl' : Bool} (hc : 0 ≤ c)
    (hpos : ∀ μ ν, Ach c β μ ν → 1 ≤ μ ∧ 0 < ν)
    (hb : b ≤ b₀) (hd : d ≤ d₀) (h : Concl2 c β b₀ d₀ b' d' fl fl') :
    Concl2 c β b d b' d' fl fl' := by
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, μ, ν, hA, h1, h2⟩
  · exact Or.inl ⟨h0, le_trans hb h1, le_trans hd h2⟩
  · obtain ⟨hμ, hν⟩ := hpos μ ν hA
    refine Or.inr ⟨h0, μ, ν, hA, ?_, ?_⟩
    · have : c * μ * b ≤ c * μ * b₀ := mul_le_mul_of_nonneg_left hb (by positivity)
      linarith
    · have : ν * d ≤ ν * d₀ := mul_le_mul_of_nonneg_left hd hν.le
      linarith

theorem segment2 {β₁ β₂ : ℝ} (hβ₁ : 1 / (r7 * (r7 - 1)) ≤ β₁) (hβ₁1 : β₁ ≤ 1)
    (hβ₂ : betaNon ≤ β₂) (hβ₂1 : β₂ ≤ 1) (L : ℕ → FLine) :
    ∀ len p k : ℕ, (∀ i, p ≤ i → i < p + len → Step2 r7 β₁ β₂ (L i) (L (i + 1))) →
      (∀ i, p ≤ i → i ≤ p + len → k + 1 ≤ (L i).bs.length ∧ 0 ≤ (L i).a) →
      (L p).bs.length = k + 1 → (L (p + len)).bs.length = k + 1 →
      Concl2 r7 β₂ (top (L p).bs) (L p).a (top (L (p + len)).bs) (L (p + len)).a
        (L p).fresh (L (p + len)).fresh := by
  obtain ⟨hβc, _, _, _, hβ1', hβ0⟩ := beta_star_conditions hβ₁ hβ₁1
  obtain ⟨_, _, _, hβ₂1', hβ₂0⟩ := beta_non_conditions hβ₂ hβ₂1
  have hc1 := one_lt_r7
  have hpos := fun μ ν (h : Ach r7 β₂ μ ν) => ach_pos hc1 hβ₂0 hβ₂1' h
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
  intro p k hstep hdep hp hq
  rcases Nat.eq_zero_or_pos len with h0 | hlen
  · subst h0
    exact Or.inl ⟨rfl, le_rfl, le_rfl⟩
  have hs0 := hstep p le_rfl (by omega)
  rcases step2_inv hs0 with ⟨h1, -, -, -⟩ |
    ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, e0, e1, ef⟩ | ⟨b, e0, -, -, -⟩ | ⟨hl, hle, ha, hf⟩
  · rw [h1] at hp; simp at hp
  · have hbs : bs.length = k := by
      rw [e0] at hp; simp only [List.length_append, List.length_singleton] at hp; omega
    have hl1 : (L (p + 1)).bs.length = k + 2 := by
      rw [e1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    classical
    have hex : ∃ j, p + 1 ≤ j ∧ j ≤ p + len ∧ (L j).bs.length = k + 1 :=
      ⟨p + len, by omega, le_rfl, hq⟩
    obtain ⟨hm1, hm2, hm3⟩ := Nat.find_spec hex
    have hmin : ∀ j, p + 1 ≤ j → j < Nat.find hex → k + 2 ≤ (L j).bs.length := by
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
    have hlA : (L (m0 - 1)).bs.length = k + 2 := by
      have h1 := hmin (m0 - 1) (by omega) (by omega)
      have h2 := (step2_len hsA).2
      omega
    rcases step2_inv hsA with ⟨h1, -, -, -⟩ | ⟨bs', b', x', b₁', b₂', -, -, -, -, -, f0, f1, -⟩ |
      ⟨y, f0, hu1, hu2, hfm⟩ | ⟨f0, -, -, -⟩
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
      have htopA : top (L (p + 1)).bs = b₂ := by
        rw [e1, show bs ++ [b₁, b₂] = (bs ++ [b₁]) ++ [b₂] by simp, top_concat]
      have htopY : top (L (m0 - 1)).bs = y := by rw [f0, top_concat]
      rw [htopA, htopY, ef] at hA
      have hmono : ∀ j, j ≤ m0 - 1 - (p + 1) →
          (L (p + 1)).bs.getD k 0 ≤ (L (p + 1 + j)).bs.getD k 0 := by
        intro j
        induction j with
        | zero => intro _; exact le_rfl
        | succ j ihj =>
          intro hj
          have hs := hstep (p + 1 + j) (by omega) (by omega)
          have := step2_getD_mono hs (hmin (p + 1 + j) (by omega) (by omega))
            (hmin (p + 1 + j + 1) (by omega) (by omega))
          exact le_trans (ihj (by omega)) this
      have hX1 : (L (p + 1)).bs.getD k 0 = b₁ := by
        rw [e1, List.getD_append_right _ _ _ _ (by omega), hbs, Nat.sub_self]; rfl
      have hX2 : (L (m0 - 1)).bs.getD k 0 = top (L m0).bs := by
        rw [f0, List.getD_append _ _ _ _ (by omega), top_eq_getD hm3]
      have hXX := hmono (m0 - 1 - (p + 1)) le_rfl
      rw [show p + 1 + (m0 - 1 - (p + 1)) = m0 - 1 by omega, hX1, hX2] at hXX
      have hbtop : top (L p).bs = b := by rw [e0, top_concat]
      rw [hbtop]
      have hBf : (top (L m0).bs ≤ top (L (p + len)).bs ∧ (L m0).a ≤ (L (p + len)).a) ∨
          ∃ μ ν, Ach r7 β₂ μ ν ∧ r7 * μ * top (L m0).bs ≤ (L (p + len)).a ∧
            ν * (L m0).a ≤ (L (p + len)).a := by
        rcases hB with ⟨_, h1, h2⟩ | ⟨_, h⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr h
      have hend : (L (p + len)).fresh = false := by
        rcases hB with ⟨h0, -, -⟩ | ⟨h0, -⟩
        · rw [h0, hfm]
        · exact h0
      refine Or.inr ⟨hend, ?_⟩
      have hXb : max x b ≤ top (L m0).bs := le_trans h₁ hXX
      have hd0 := (hdep p le_rfl (by omega)).2
      rcases hA with ⟨hfa, hy, hz⟩ | ⟨hfa, μ₂, ν₂, hA₂, hz1, hz2⟩
      · rw [hfa] at hu2
        simp only [if_true] at hu2
        exact combine_imm hc1 hβ0 hβ1' hβc hpos hd0 hx hXb h₂ h₃ hy hz hu1 hu2 hBf
      · rw [hfa] at hu2
        simp only [Bool.false_eq_true, if_false] at hu2
        exact combine_non hc1 hβ₂0 hβ₂1' hx hxa hXb h₂ h₃ hA₂ hz1 hz2 hu1 hu2 hBf
    · rw [f0] at hm3; omega
  · have := (hdep (p + 1) (by omega) (by omega)).1
    rw [e0] at hp
    simp only [List.length_append, List.length_singleton] at hp this
    omega
  · have hl1 : (L (p + 1)).bs.length = k + 1 := by rw [hl, hp]
    have hrest := ih (len - 1) (by omega) (p + 1) k
      (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => hdep i (by omega) (by omega)) hl1 (by
        rw [show p + 1 + (len - 1) = p + len by omega]; exact hq)
    rw [show p + 1 + (len - 1) = p + len by omega, hf] at hrest
    have htop : top (L p).bs ≤ top (L (p + 1)).bs := by
      rw [top_eq_getD hp, top_eq_getD hl1]; exact hle k
    exact concl2_weak (by linarith) hpos htop ha hrest

theorem no_refutation2_r7 {β₁ β₂ : ℝ} (hβ₁ : 1 / (r7 * (r7 - 1)) ≤ β₁) (hβ₁1 : β₁ ≤ 1)
    (hβ₂ : betaNon ≤ β₂) (hβ₂1 : β₂ ≤ 1) (n : ℕ) (L : ℕ → FLine) :
    ¬ RefutesWith2 (Step2 r7 β₁ β₂) n L := by
  rintro ⟨hn, h0, hN, ha, hlt, hstep, hmid⟩
  have hc1 := one_lt_r7
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).a := by
    intro i
    induction i with
    | zero => intro _; exact ha
    | succ i ih => intro hi; exact step2_nonneg (by linarith) (hstep i (by omega)) (ih (by omega))
  rcases step2_inv (hstep 0 (by omega)) with ⟨-, h1, h2, -⟩ |
    ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -, -⟩ | ⟨b, e0, -, -, -⟩ | ⟨hl, -, ha', -⟩
  · rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · have hsN := hstep (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega] at hsN
      have hmidN := hmid (n - 1) (by omega) (by omega)
      rcases step2_inv hsN with ⟨g1, -, -, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, -, g1, -⟩ |
        ⟨y, g0, hu1, -, -⟩ | ⟨g1, -, -, -⟩
      · exact hmidN g1
      · rw [hN] at g1; simp at g1
      · have hlen1 : (L (n - 1)).bs.length = 0 + 1 := by rw [g0, hN]; rfl
        have hseg := segment2 hβ₁ hβ₁1 hβ₂ hβ₂1 L (n - 2) 1 0
          (fun i h1 h2 => hstep i (by omega))
          (fun i h1 h2 => ⟨by
            have := hmid i (by omega) (by omega)
            exact Nat.one_le_iff_ne_zero.mpr (fun h => this (List.length_eq_zero_iff.mp h)),
            hnn i (by omega)⟩)
          (by rw [h1]; rfl) (by rw [show 1 + (n - 2) = n - 1 by omega]; exact hlen1)
        rw [show 1 + (n - 2) = n - 1 by omega, h1, h2] at hseg
        have hy : top (L (n - 1)).bs = y := by rw [g0, top_concat]
        rw [hy] at hseg
        have he : r7 * (L (n - 1)).a ≤ (L n).a := by
          have := mul_le_mul_of_nonneg_left (le_max_right y (L (n - 1)).a) (by linarith : (0:ℝ) ≤ r7)
          linarith
        rcases hseg with ⟨-, -, hd⟩ | ⟨-, μ, ν, hA, -, hd⟩
        · nlinarith
        · have hν := (ach_inv2 hβ₂ hβ₂1 hA).2.2.2
          have hτ := tau0_ge_inv (le_refl r7)
          have hrν : 1 < r7 * ν := by
            have h7 : 0 < r7 := by linarith
            have := mul_lt_mul_of_pos_left (lt_of_le_of_lt hτ hν) h7
            rwa [mul_one_div_cancel h7.ne'] at this
          nlinarith
      · rw [hN] at g1; simp at g1; exact hmidN (List.length_eq_zero_iff.mp g1.symm)
    · have : n = 1 := by omega
      subst this
      rw [h1] at hN; simp at hN
  · rw [h0] at e0; simp at e0
  · rw [h0] at e0; simp at e0
  · rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · exact hmid 1 (by omega) hn1 (List.length_eq_zero_iff.mp (by rw [hl, h0]; rfl))
    · have : n = 1 := by omega
      subst this
      linarith

theorem betaNon_le_one : betaNon ≤ 1 := by
  have h1 := one_lt_r7
  have h2 := r7_lt_two
  unfold betaNon
  rw [div_le_one (by linarith)]
  nlinarith [cub_r7, one_le_r7r7m1]

theorem no_refutation2 {c β₁ β₂ : ℝ} (hc : r7 ≤ c) (hβ₁ : 1 / (r7 * (r7 - 1)) ≤ β₁)
    (hβ₂ : betaNon ≤ β₂) (n : ℕ) (L : ℕ → FLine) : ¬ RefutesWith2 (Step2 c β₁ β₂) n L := by
  intro h
  have h1 := one_lt_r7
  have hs1 : 1 / (r7 * (r7 - 1)) ≤ 1 := by
    rw [div_le_one (by linarith [one_le_r7r7m1])]; exact one_le_r7r7m1
  have hn1 := betaNon_le_one
  have hn0 : 0 ≤ betaNon := by unfold betaNon; apply div_nonneg <;> nlinarith [r7_lt_two]
  have hg1 : 0 ≤ min β₁ 1 := le_min (le_trans (by positivity) hβ₁) zero_le_one
  have hg2 : 0 ≤ min β₂ 1 := le_min (le_trans hn0 hβ₂) zero_le_one
  apply no_refutation2_r7 (β₁ := min β₁ 1) (β₂ := min β₂ 1) (le_min hβ₁ hs1) (min_le_right _ _)
    (le_min hβ₂ hn1) (min_le_right _ _) n L
  exact refutes2_mono (fun L L' hL hs =>
    ⟨step2_restrict hc h1.le hg1 hg2 (min_le_left _ _) (min_le_left _ _) hs hL,
      step2_nonneg (by linarith) hs hL⟩) h

theorem betaNon_lt_betaStar : betaNon < 1 / (r7 * (r7 - 1)) := by
  have h1 := one_lt_r7
  have h2 := r7_lt_two
  have hc := cub_r7
  unfold cub at hc
  unfold betaNon
  have hr1 : 0 < r7 - 1 := by linarith
  have hp : 0 < r7 * (r7 - 1) := by positivity
  rw [div_lt_div_iff₀ hr1 hp]
  nlinarith

theorem fvm_iteration_threshold {c β : ℝ} (hc1 : 1 < c) (hγ : 0 < gam c β) :
    (c - 1) / gam c β < 1 / c ↔ β < c * (2 - c) / (c - 1) := by
  have hc0 : 0 < c := by linarith
  have hcm : 0 < c - 1 := by linarith
  unfold gam at hγ ⊢
  rw [div_lt_div_iff₀ hγ hc0, lt_div_iff₀ hcm]
  constructor <;> intro h <;> nlinarith

end PastaMath.SatBarriers
