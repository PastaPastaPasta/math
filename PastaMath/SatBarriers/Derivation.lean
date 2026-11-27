-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Chain
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Find

namespace PastaMath.SatBarriers

abbrev RLine := List ℝ × ℝ

def top (l : List ℝ) : ℝ := l.getD (l.length - 1) 0

inductive Step (c β : ℝ) : RLine → RLine → Prop
  | init (a : ℝ) : Step c β ([], a) ([0], a)
  | speed (bs : List ℝ) (b a x b₁ b₂ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a) (h₁ : max x b ≤ b₁)
      (h₂ : b ≤ b₂) (h₃ : a - x ≤ a₂) : Step c β (bs ++ [b], a) (bs ++ [b₁, b₂], a₂)
  | slow (bs : List ℝ) (b a e : ℝ) (h₁ : c * max b a ≤ e)
      (h₂ : top bs + β * (c - 1) * max b a ≤ e) : Step c β (bs ++ [b], a) (bs, e)
  | weak (bs bs' : List ℝ) (a a' : ℝ) (hl : bs'.length = bs.length)
      (hle : ∀ i, bs.getD i 0 ≤ bs'.getD i 0) (ha : a ≤ a') : Step c β (bs, a) (bs', a')

def RefutesWith (R : RLine → RLine → Prop) (n : ℕ) (L : ℕ → RLine) : Prop :=
  1 ≤ n ∧ (L 0).1 = [] ∧ (L n).1 = [] ∧ 0 ≤ (L 0).2 ∧ (L n).2 < (L 0).2 ∧
    (∀ i < n, R (L i) (L (i + 1))) ∧ (∀ i, 0 < i → i < n → (L i).1 ≠ [])

inductive Ach (c β : ℝ) : ℝ → ℝ → Prop
  | base : Ach c β 1 (c - 1)
  | big {μ ν : ℝ} : 1 ≤ μ → 1 ≤ ν → Ach c β μ ν
  | dbeta {μ ν : ℝ} : Ach c β μ ν → Ach c β (c * μ) (c * ν / (1 + gam c β * ν))
  | comp {μ₁ ν₁ μ₂ ν₂ : ℝ} : Ach c β μ₁ ν₁ → Ach c β μ₂ ν₂ →
      Ach c β (max μ₁ (c * ν₁ * μ₂)) (c * μ₁ * ν₁ * ν₂ / (μ₁ + ν₁ * ν₂))

def Concl (c β b d b' d' : ℝ) : Prop :=
  (b ≤ b' ∧ d ≤ d') ∨ ∃ μ ν, Ach c β μ ν ∧ c * μ * b ≤ d' ∧ ν * d ≤ d'

theorem top_concat (bs : List ℝ) (b : ℝ) : top (bs ++ [b]) = b := by
  unfold top
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

theorem top_eq_getD {l : List ℝ} {k : ℕ} (h : l.length = k + 1) : top l = l.getD k 0 := by
  unfold top
  rw [h, Nat.add_sub_cancel]

theorem step_inv {c β : ℝ} {L L' : RLine} (h : Step c β L L') :
    (L.1 = [] ∧ L'.1 = [0] ∧ L'.2 = L.2) ∨
    (∃ (bs : List ℝ) (b x b₁ b₂ : ℝ), 0 ≤ x ∧ x ≤ L.2 ∧ max x b ≤ b₁ ∧ b ≤ b₂ ∧
      L.2 - x ≤ L'.2 ∧ L.1 = bs ++ [b] ∧ L'.1 = bs ++ [b₁, b₂]) ∨
    (∃ b : ℝ, L.1 = L'.1 ++ [b] ∧ c * max b L.2 ≤ L'.2 ∧
      top L'.1 + β * (c - 1) * max b L.2 ≤ L'.2) ∨
    (L'.1.length = L.1.length ∧ (∀ i, L.1.getD i 0 ≤ L'.1.getD i 0) ∧ L.2 ≤ L'.2) := by
  cases h with
  | init a => exact Or.inl ⟨rfl, rfl, rfl⟩
  | speed bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact Or.inr (Or.inl ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, rfl, rfl⟩)
  | slow bs b a e h₁ h₂ => exact Or.inr (Or.inr (Or.inl ⟨b, rfl, h₁, h₂⟩))
  | weak bs bs' a a' hl hle ha => exact Or.inr (Or.inr (Or.inr ⟨hl, hle, ha⟩))

theorem step_len {c β : ℝ} {L L' : RLine} (h : Step c β L L') :
    L'.1.length ≤ L.1.length + 1 ∧ L.1.length ≤ L'.1.length + 1 := by
  rcases step_inv h with ⟨h1, h2, _⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, h1, h2⟩ |
    ⟨b, h1, -, -⟩ | ⟨h1, -, -⟩
  · rw [h1, h2]; simp
  · rw [h1, h2]; simp
  · rw [h1]; simp only [List.length_append, List.length_singleton]; omega
  · omega

theorem step_getD_mono {c β : ℝ} {L L' : RLine} (h : Step c β L L') {k : ℕ}
    (hk : k + 2 ≤ L.1.length) (hk' : k + 2 ≤ L'.1.length) :
    L.1.getD k 0 ≤ L'.1.getD k 0 := by
  rcases step_inv h with ⟨h1, -, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, h1, h2⟩ |
    ⟨b, h1, -, -⟩ | ⟨-, hle, -⟩
  · rw [h1] at hk; simp at hk
  · rw [h1] at hk ⊢
    rw [h2]
    simp only [List.length_append, List.length_singleton] at hk
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · rw [h1]
    rw [List.getD_append _ _ _ _ (by omega)]
  · exact hle k

theorem step_nonneg {c β : ℝ} (hc : 0 ≤ c) {L L' : RLine} (h : Step c β L L')
    (hL : 0 ≤ L.2) : 0 ≤ L'.2 := by
  rcases step_inv h with ⟨-, -, h3⟩ | ⟨bs, b, x, b₁, b₂, -, hxa, -, -, h3, -, -⟩ |
    ⟨b, -, h3, -⟩ | ⟨-, -, h3⟩
  · rw [h3]; exact hL
  · linarith
  · have : 0 ≤ c * max b L.2 := mul_nonneg hc (le_trans hL (le_max_right _ _))
    linarith
  · linarith

theorem step_restrict {c β c₀ β₀ : ℝ} (hc : c₀ ≤ c) (hc₀ : 1 ≤ c₀) (hβ₀ : 0 ≤ β₀)
    (hββ : β₀ ≤ β) {L L' : RLine} (h : Step c β L L') (hL : 0 ≤ L.2) : Step c₀ β₀ L L' := by
  cases h with
  | init a => exact Step.init a
  | speed bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ => exact Step.speed bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃
  | weak bs bs' a a' hl hle ha => exact Step.weak bs bs' a a' hl hle ha
  | slow bs b a e h₁ h₂ =>
    have hM : 0 ≤ max b a := le_trans hL (le_max_right _ _)
    apply Step.slow bs b a e
    · exact le_trans (mul_le_mul_of_nonneg_right hc hM) h₁
    · have e1 : β₀ * (c₀ - 1) ≤ β * (c - 1) := by
        apply mul_le_mul hββ (by linarith) (by linarith) (by linarith)
      have := mul_le_mul_of_nonneg_right e1 hM
      linarith

theorem refutes_mono {R R' : RLine → RLine → Prop}
    (hR : ∀ L L', 0 ≤ L.2 → R L L' → R' L L' ∧ 0 ≤ L'.2) {n : ℕ} {L : ℕ → RLine}
    (h : RefutesWith R n L) : RefutesWith R' n L := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).2 := by
    intro i
    induction i with
    | zero => intro _; exact h4
    | succ i ih =>
      intro hi
      exact (hR _ _ (ih (by omega)) (h6 i (by omega))).2
  exact ⟨h1, h2, h3, h4, h5, fun i hi => (hR _ _ (hnn i hi.le) (h6 i hi)).1, h7⟩

theorem ach_pos {c β : ℝ} (hc1 : 1 < c) (_hβ0 : 0 ≤ β) (hβ1 : β * (c - 1) ≤ 1) {μ ν : ℝ}
    (h : Ach c β μ ν) : 1 ≤ μ ∧ 0 < ν := by
  induction h with
  | base => exact ⟨le_rfl, by linarith⟩
  | big hμ hν => exact ⟨hμ, by linarith⟩
  | @dbeta μ ν _ ih =>
    obtain ⟨h1, h2⟩ := ih
    have hγ : 0 < gam c β := by unfold gam; linarith
    refine ⟨by nlinarith, ?_⟩
    have : 0 < 1 + gam c β * ν := by positivity
    have : 0 < c := by linarith
    positivity
  | @comp μ₁ ν₁ μ₂ ν₂ _ _ ih1 ih2 =>
    obtain ⟨a1, a2⟩ := ih1
    obtain ⟨b1, b2⟩ := ih2
    refine ⟨le_trans a1 (le_max_left _ _), ?_⟩
    have : (0 : ℝ) < μ₁ := by linarith
    have : 0 < c := by linarith
    positivity

theorem ach_inv {β : ℝ} (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hβ1 : β ≤ 1) {μ ν : ℝ}
    (h : Ach r7 β μ ν) : Inv r7 μ ν := by
  obtain ⟨_, hii, hiii, hγ, _, _⟩ := beta_star_conditions hβ hβ1
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

theorem concl_mono {c β b d b₀ d₀ b' d' : ℝ} (hc : 0 ≤ c) (hpos : ∀ μ ν, Ach c β μ ν → 1 ≤ μ ∧ 0 < ν)
    (hb : b ≤ b₀) (hd : d ≤ d₀) (h : Concl c β b₀ d₀ b' d') : Concl c β b d b' d' := by
  rcases h with ⟨h1, h2⟩ | ⟨μ, ν, hA, h1, h2⟩
  · exact Or.inl ⟨le_trans hb h1, le_trans hd h2⟩
  · obtain ⟨hμ, hν⟩ := hpos μ ν hA
    refine Or.inr ⟨μ, ν, hA, ?_, ?_⟩
    · have : c * μ * b ≤ c * μ * b₀ := mul_le_mul_of_nonneg_left hb (by positivity)
      linarith
    · have : ν * d ≤ ν * d₀ := mul_le_mul_of_nonneg_left hd hν.le
      linarith

theorem combine {c β : ℝ} (hc1 : 1 < c) (hβ0 : 0 ≤ β) (hβ1 : β * (c - 1) ≤ 1)
    (hβc : (c - 1) * (1 + gam c β) ≤ c)
    {b d x X b₂ a₂ y z u b' d' : ℝ} (hd : 0 ≤ d) (hx : 0 ≤ x) (hxd : x ≤ d)
    (hX : max x b ≤ X) (hb₂ : b ≤ b₂) (ha₂ : d - x ≤ a₂)
    (hA : Concl c β b₂ a₂ y z) (hu1 : c * max y z ≤ u) (hu2 : X + β * (c - 1) * max y z ≤ u)
    (hB : Concl c β X u b' d') :
    ∃ μ ν, Ach c β μ ν ∧ c * μ * b ≤ d' ∧ ν * d ≤ d' := by
  have hpos := fun μ ν (h : Ach c β μ ν) => ach_pos hc1 hβ0 hβ1 h
  have hc0 : 0 < c := by linarith
  have hβc0 : 0 ≤ β * (c - 1) := mul_nonneg hβ0 (by linarith)
  have hxX : x ≤ X := le_trans (le_max_left _ _) hX
  have hbX : b ≤ X := le_trans (le_max_right _ _) hX
  have hyz : z ≤ max y z := le_max_right _ _
  rcases hA with ⟨hy, hz⟩ | ⟨μ₂, ν₂, hA₂, hz1, hz2⟩
  · have hm : max b (d - x) ≤ max y z :=
      max_le_max (le_trans hb₂ hy) (le_trans ha₂ hz)
    have hcz : c * (d - x) ≤ u := by
      have := mul_le_mul_of_nonneg_left (le_trans (le_max_right b (d - x)) hm) hc0.le
      linarith
    rcases hB with ⟨_, hud⟩ | ⟨μ₁, ν₁, hA₁, hd1, hd2⟩
    · have key : max (c * max b (d - x)) (x + β * (c - 1) * max b (d - x)) ≤ u := by
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
  · obtain ⟨hμ₂, hν₂⟩ := hpos _ _ hA₂
    have hz1' : c * μ₂ * b ≤ z := by
      have : c * μ₂ * b ≤ c * μ₂ * b₂ := mul_le_mul_of_nonneg_left hb₂ (by positivity)
      linarith
    have hz2' : ν₂ * (d - x) ≤ z := by
      have : ν₂ * (d - x) ≤ ν₂ * a₂ := mul_le_mul_of_nonneg_left ha₂ hν₂.le
      linarith
    have hcz : c * z ≤ u := le_trans (mul_le_mul_of_nonneg_left hyz hc0.le) hu1
    have hu : max (c * z) (x + β * (c - 1) * z) ≤ u := by
      apply max_le hcz
      have := mul_le_mul_of_nonneg_left hyz hβc0
      linarith
    rcases hB with ⟨_, hud⟩ | ⟨μ₁, ν₁, hA₁, hd1, hd2⟩
    · rcases le_or_gt (β * (c - 1) * ν₂) 1 with hβν | hβν
      · have k := btrivial_bound_beta hc1 hν₂ hβ0 hβν hz2' hu
        refine ⟨c * μ₂, c * ν₂ / (1 + gam c β * ν₂), Ach.dbeta hA₂, ?_, ?_⟩
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

theorem segment {β : ℝ} (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hβ1 : β ≤ 1) (L : ℕ → RLine) :
    ∀ len p k : ℕ, (∀ i, p ≤ i → i < p + len → Step r7 β (L i) (L (i + 1))) →
      (∀ i, p ≤ i → i ≤ p + len → k + 1 ≤ (L i).1.length ∧ 0 ≤ (L i).2) →
      (L p).1.length = k + 1 → (L (p + len)).1.length = k + 1 →
      Concl r7 β (top (L p).1) (L p).2 (top (L (p + len)).1) (L (p + len)).2 := by
  obtain ⟨hβc, _, _, _, hβ1', hβ0⟩ := beta_star_conditions hβ hβ1
  have hc1 := one_lt_r7
  have hpos := fun μ ν (h : Ach r7 β μ ν) => ach_pos hc1 hβ0 hβ1' h
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

theorem one_le_r7r7m1 : 1 ≤ r7 * (r7 - 1) := by
  have hc := cub_r7
  unfold cub at hc
  have h1 := one_lt_r7
  by_contra h
  push Not at h
  have : r7 * (r7 ^ 2 - r7 - 1) < 0 := mul_neg_of_pos_of_neg (by linarith) (by nlinarith)
  nlinarith

theorem no_refutation_r7 {β : ℝ} (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hβ1 : β ≤ 1)
    (n : ℕ) (L : ℕ → RLine) : ¬ RefutesWith (Step r7 β) n L := by
  rintro ⟨hn, h0, hN, ha, hlt, hstep, hmid⟩
  obtain ⟨_, _, _, _, hβ1', hβ0⟩ := beta_star_conditions hβ hβ1
  have hc1 := one_lt_r7
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).2 := by
    intro i
    induction i with
    | zero => intro _; exact ha
    | succ i ih => intro hi; exact step_nonneg (by linarith) (hstep i (by omega)) (ih (by omega))
  rcases step_inv (hstep 0 (by omega)) with ⟨-, h1, h2⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -⟩ |
    ⟨b, e0, -, -⟩ | ⟨hl, -, ha'⟩
  · rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · have hsN := hstep (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega] at hsN
      have hmidN := hmid (n - 1) (by omega) (by omega)
      rcases step_inv hsN with ⟨g1, -, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, -, g1⟩ |
        ⟨y, g0, hu1, -⟩ | ⟨g1, -, -⟩
      · exact hmidN g1
      · rw [hN] at g1; simp at g1
      · have hlen1 : (L (n - 1)).1.length = 0 + 1 := by rw [g0, hN]; rfl
        have hseg := segment hβ hβ1 L (n - 2) 1 0
          (fun i h1 h2 => hstep i (by omega))
          (fun i h1 h2 => ⟨by
            have := hmid i (by omega) (by omega)
            exact Nat.one_le_iff_ne_zero.mpr (fun h => this (List.length_eq_zero_iff.mp h)),
            hnn i (by omega)⟩)
          (by rw [h1]; rfl) (by rw [show 1 + (n - 2) = n - 1 by omega]; exact hlen1)
        rw [show 1 + (n - 2) = n - 1 by omega, h1, h2] at hseg
        have hy : top (L (n - 1)).1 = y := by rw [g0, top_concat]
        rw [hy] at hseg
        have he : r7 * (L (n - 1)).2 ≤ (L n).2 := by
          have := mul_le_mul_of_nonneg_left (le_max_right y (L (n - 1)).2) (by linarith : (0:ℝ) ≤ r7)
          linarith
        rcases hseg with ⟨-, hd⟩ | ⟨μ, ν, hA, -, hd⟩
        · nlinarith
        · have hν := (ach_inv hβ hβ1 hA).2.2.2
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

theorem no_refutation {c β : ℝ} (hc : r7 ≤ c) (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (n : ℕ)
    (L : ℕ → RLine) : ¬ RefutesWith (Step c β) n L := by
  intro h
  have h1 := one_lt_r7
  have hβ0 : 0 ≤ min β 1 := le_min (le_trans (by positivity) hβ) zero_le_one
  apply no_refutation_r7 (β := min β 1) (le_min hβ (by
    rw [div_le_one (by linarith [one_le_r7r7m1])]; exact one_le_r7r7m1)) (min_le_right _ _) n L
  exact refutes_mono (fun L L' hL hs =>
    ⟨step_restrict hc h1.le hβ0 (min_le_left _ _) hs hL,
      step_nonneg (by linarith) hs hL⟩) h

inductive StepS (S : ℝ → ℝ → ℝ) : RLine → RLine → Prop
  | init (a : ℝ) : StepS S ([], a) ([0], a)
  | speed (bs : List ℝ) (b a x : ℝ) (hx : 0 < x) (hxa : x ≤ a) :
      StepS S (bs ++ [b], a) (bs ++ [max x b, b], a - x)
  | slow (bs : List ℝ) (b a : ℝ) : StepS S (bs ++ [b], a) (bs, S (top bs) (max b a))
  | weak (bs bs' : List ℝ) (a a' : ℝ) (hl : bs'.length = bs.length)
      (hle : ∀ i, bs.getD i 0 ≤ bs'.getD i 0) (ha : a ≤ a') : StepS S (bs, a) (bs', a')

theorem stepS_step {c β : ℝ} {S : ℝ → ℝ → ℝ} (hS2 : ∀ B M, c * M ≤ S B M)
    (hS3 : ∀ B M, B + β * (c - 1) * M ≤ S B M) {L L' : RLine} (h : StepS S L L') :
    Step c β L L' := by
  cases h with
  | init a => exact Step.init a
  | speed bs b a x hx hxa => exact Step.speed bs b a x _ _ _ hx.le hxa le_rfl le_rfl le_rfl
  | slow bs b a => exact Step.slow bs b a _ (hS2 _ _) (hS3 _ _)
  | weak bs bs' a a' hl hle ha => exact Step.weak bs bs' a a' hl hle ha

theorem e1beta_limit {c β : ℝ} {S : ℝ → ℝ → ℝ} (hc : r7 ≤ c) (hβ : 1 / (r7 * (r7 - 1)) ≤ β)
    (hS2 : ∀ B M, c * M ≤ S B M) (hS3 : ∀ B M, B + β * (c - 1) * M ≤ S B M)
    (n : ℕ) (L : ℕ → RLine) : ¬ RefutesWith (StepS S) n L := by
  intro h
  have hc0 : 0 ≤ c := by linarith [one_lt_r7]
  apply no_refutation hc hβ n L
  exact refutes_mono (fun L L' hL hs => ⟨stepS_step hS2 hS3 hs,
    step_nonneg hc0 (stepS_step hS2 hS3 hs) hL⟩) h

theorem bw_limit {c : ℝ} (hc : r7 ≤ c) (n : ℕ) (L : ℕ → RLine) :
    ¬ RefutesWith (StepS (fun B M => c * max B M)) n L := by
  have h1 := one_lt_r7
  have hβ : 1 / (r7 * (r7 - 1)) ≤ 1 := by
    rw [div_le_one (by linarith [one_le_r7r7m1])]; exact one_le_r7r7m1
  apply e1beta_limit hc hβ _ _ n L
  · intro B M
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  · intro B M
    have hB := le_max_left B M
    have hM := le_max_right B M
    nlinarith

theorem slowEnvelope_limit {c β : ℝ} {S : ℝ → ℝ → ℝ} (hc : r7 ≤ c)
    (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (hS : SlowEnvelope c β S) (n : ℕ) (L : ℕ → RLine) :
    ¬ RefutesWith (StepS S) n L :=
  e1beta_limit hc hβ hS.lowerM hS.lowerB n L

noncomputable def lvLines : ℕ → RLine
  | 0 => ([], 1)
  | 1 => ([0], 1)
  | 2 => ([1 / 2, 0], 1 / 2)
  | 3 => ([1 / 2], 7 / 10)
  | _ => ([], 49 / 50)

theorem lv_refutation : RefutesWith (StepS (fun B M => (7 / 5 : ℝ) * max B M)) 4 lvLines := by
  refine ⟨by norm_num, rfl, rfl, by norm_num [lvLines], by norm_num [lvLines], ?_, ?_⟩
  · intro i hi
    rcases i with _ | _ | _ | _ | i
    · exact StepS.init 1
    · have h := StepS.speed (S := fun B M => (7 / 5 : ℝ) * max B M) [] 0 1 (1 / 2)
        (by norm_num) (by norm_num)
      have e1 : (max (1 / 2 : ℝ) 0) = 1 / 2 := by norm_num
      have e2 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [e1, e2] at h
      exact h
    · have h := StepS.slow (S := fun B M => (7 / 5 : ℝ) * max B M) [1 / 2] 0 (1 / 2)
      have e : (7 / 5 : ℝ) * max (top [1 / 2]) (max 0 (1 / 2)) = 7 / 10 := by
        simp only [top, List.length_singleton, Nat.sub_self, List.getD_cons_zero]
        norm_num
      show StepS _ ([1 / 2] ++ [0], 1 / 2) ([1 / 2], 7 / 10)
      rw [← e]; exact h
    · have h := StepS.slow (S := fun B M => (7 / 5 : ℝ) * max B M) [] (1 / 2) (7 / 10)
      have e : (7 / 5 : ℝ) * max (top []) (max (1 / 2) (7 / 10)) = 49 / 50 := by
        simp only [top, List.length_nil, Nat.zero_sub, List.getD_nil]
        norm_num
      show StepS _ ([] ++ [1 / 2], 7 / 10) ([], 49 / 50)
      rw [← e]; exact h
    · omega
  · intro i h1 h2
    rcases i with _ | _ | _ | _ | i
    · omega
    · simp [lvLines]
    · simp [lvLines]
    · simp [lvLines]
    · omega

theorem lv_threshold_check : (7 / 5 : ℝ) < r7 := by
  have h := cub_r7
  unfold cub at h
  have h1 := one_lt_r7
  by_contra hh
  push Not at hh
  nlinarith [sq_nonneg (r7 - 1)]

end PastaMath.SatBarriers
