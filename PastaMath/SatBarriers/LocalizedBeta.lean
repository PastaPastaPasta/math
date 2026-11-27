-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Localized

namespace PastaMath.SatBarriers

noncomputable def PsiB (c β b d l : ℝ) : ℝ :=
  min (max b d) (max (max (b + β * (c - 1) * l) (c * l)) ((d + l) / c))

theorem psiB_mono {c β b d l b' d' l' : ℝ} (hc : 1 ≤ c) (hβ : 0 ≤ β) (hb : b ≤ b') (hd : d ≤ d')
    (hl : l ≤ l') : PsiB c β b d l ≤ PsiB c β b' d' l' := by
  unfold PsiB
  have hc0 : 0 < c := by linarith
  have hk : 0 ≤ β * (c - 1) := mul_nonneg hβ (by linarith)
  apply min_le_min (max_le_max hb hd)
  apply max_le_max (max_le_max ?_ ?_)
  · exact div_le_div_of_nonneg_right (by linarith) hc0.le
  · have := mul_le_mul_of_nonneg_left hl hk
    linarith
  · exact mul_le_mul_of_nonneg_left hl hc0.le

theorem psiB_le_max {c β b d l : ℝ} : PsiB c β b d l ≤ max b d := min_le_left _ _

theorem psiB_diag_ge {c β l D : ℝ} (hc : 1 ≤ c) (hl : 0 ≤ l) : l ≤ PsiB c β l D l := by
  unfold PsiB
  apply le_min (le_max_left _ _)
  apply le_trans _ (le_max_left _ _)
  apply le_trans _ (le_max_right _ _)
  nlinarith

theorem psiB_top {c β a l : ℝ} (hc : 1 ≤ c) (ha : 0 ≤ a) (hl : 0 ≤ l) :
    a / c ≤ PsiB c β 0 a l := by
  unfold PsiB
  have hc0 : 0 < c := by linarith
  apply le_min
  · rw [div_le_iff₀ hc0]; simp only [max_eq_right ha]; nlinarith
  · apply le_trans _ (le_max_right _ _)
    exact div_le_div_of_nonneg_right (by linarith) hc0.le

theorem threshB_consequences {c β : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hcub : (1 - β) * (c - 1) ^ 2 ≤ cub c) :
    0 ≤ c ^ 2 - c - 2 + β * (c - 1) ∧ 0 ≤ c ^ 2 - 2 * c + β * (c - 1) ∧
      0 ≤ 1 - β * (c - 1) ∧ 2 * c - 1 ≤ (c - 1) ^ 2 * (c ^ 2 + c * β - 1) ∧
      0 ≤ c * β * (c - 1) - 1 + (c ^ 2 - 1) * (c - 1) := by
  unfold cub at hcub
  have hc1 : 0 < c - 1 := by linarith
  have hgap : 0 ≤ (c ^ 3 - c ^ 2 - 2 * c + 1) - (1 - β) * (c - 1) ^ 2 := by linarith
  have id1 : (c - 1) * (c ^ 2 - c - 2 + β * (c - 1)) =
      (2 - c) + ((c ^ 3 - c ^ 2 - 2 * c + 1) - (1 - β) * (c - 1) ^ 2) := by ring
  have k1 : 0 ≤ (c - 1) * (c ^ 2 - c - 2 + β * (c - 1)) := by rw [id1]; linarith
  have k1' : 0 ≤ c ^ 2 - c - 2 + β * (c - 1) := by
    by_contra h
    push Not at h
    have := mul_neg_of_pos_of_neg hc1 h
    linarith
  have hb1 : β * (c - 1) ≤ 1 * (c - 1) := mul_le_mul_of_nonneg_right hβ1 hc1.le
  have id2 : (c - 1) ^ 2 * (c ^ 2 + c * β - 1) - (2 * c - 1) =
      c * ((c ^ 3 - c ^ 2 - 2 * c + 1) - (1 - β) * (c - 1) ^ 2) := by ring
  have k4 : 0 ≤ c * ((c ^ 3 - c ^ 2 - 2 * c + 1) - (1 - β) * (c - 1) ^ 2) :=
    mul_nonneg (by linarith) hgap
  have hsq : 81 / 25 ≤ c ^ 2 := by nlinarith
  have hpr : (56 / 25) * (4 / 5) ≤ (c ^ 2 - 1) * (c - 1) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hcb : 0 ≤ c * β * (c - 1) := mul_nonneg (mul_nonneg (by linarith) hβ0) hc1.le
  refine ⟨k1', by linarith, by linarith, by linarith, by linarith⟩

theorem psiB_step_gen {c β b d l x M u l' X : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hcub : (1 - β) * (c - 1) ^ 2 ≤ cub c)
    (hl : 0 ≤ l) (_hx : 0 ≤ x) (hxd : x ≤ d) (hXx : x ≤ X) (hXb : b ≤ X)
    (hM : PsiB c β l (d - x) l ≤ M) (hu1 : c * M ≤ u) (hu2x : x + β * (c - 1) * M ≤ u)
    (hu2b : b + β * (c - 1) * l ≤ u)
    (hl1 : l ≤ l') (hl2 : x + c * M ≤ u + l') : PsiB c β b d l ≤ PsiB c β X u l' := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := threshB_consequences hc hc2 hβ0 hβ1 hcub
  have hc0 : 0 < c := by linarith
  have hc1 : 0 ≤ c - 1 := by linarith
  have hk : 0 ≤ β * (c - 1) := mul_nonneg hβ0 hc1
  have hl'0 : 0 ≤ l' := le_trans hl hl1
  set D := d - x with hD
  have hD0 : 0 ≤ D := by linarith
  have hMl : l ≤ M := le_trans (psiB_diag_ge (by linarith) hl) hM
  have hA : (l ≤ M ∧ D ≤ M) ∨ (c * l ≤ M ∧ D + l ≤ c * M) := by
    unfold PsiB at hM
    rcases min_le_iff.mp hM with h | h
    · exact Or.inl ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩
    · refine Or.inr ⟨le_trans (le_max_right _ _) (le_trans (le_max_left _ _) h), ?_⟩
      have h3 := le_trans (le_max_right _ _) h
      rwa [div_le_iff₀ hc0, mul_comm] at h3
  have hfrac : ∀ z : ℝ, (d + l) / c ≤ z ↔ d + l ≤ c * z := fun z => by
    rw [div_le_iff₀ hc0, mul_comm]
  have hT1 : b + β * (c - 1) * l ≤ u := hu2b
  have hT2 : c * l ≤ c * M := mul_le_mul_of_nonneg_left hMl hc0.le
  have hM0 : 0 ≤ M := le_trans hl hMl
  have hu0 : 0 ≤ u := le_trans (mul_nonneg hc0.le hM0) hu1
  unfold PsiB
  apply le_min
  · rcases le_or_gt d b with hbd | hbd
    · apply le_trans (min_le_left _ _)
      rw [max_eq_left hbd]
      exact le_trans hXb (le_max_left _ _)
    apply le_trans _ (le_max_right X u)
    apply le_trans (min_le_right _ _)
    refine max_le (max_le (by linarith) (by linarith)) ?_
    rw [hfrac]
    rcases hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
    · rcases le_total d ((c ^ 2 - 1) * l) with hcl | hcl
      · have f1 : c * (c * M) ≤ c * u := mul_le_mul_of_nonneg_left hu1 hc0.le
        have f2 : c * (c * l) ≤ c * (c * M) := mul_le_mul_of_nonneg_left hT2 hc0.le
        linarith
      · have e1 : c * D ≤ u := le_trans (mul_le_mul_of_nonneg_left hA2 hc0.le) hu1
        have e2 : x + β * (c - 1) * D ≤ u := by
          have := mul_le_mul_of_nonneg_left hA2 hk
          linarith
        have f1 : (1 - β * (c - 1)) * (c * D) ≤ (1 - β * (c - 1)) * u :=
          mul_le_mul_of_nonneg_left e1 k3
        have f2 : c * (x + β * (c - 1) * D) ≤ c * u := mul_le_mul_of_nonneg_left e2 hc0.le
        have e3 : c * d ≤ (c + (1 - β * (c - 1))) * u := by
          have : c * d = (1 - β * (c - 1)) * (c * D) + c * (x + β * (c - 1) * D) := by
            rw [hD]; ring
          rw [this]; linarith
        have e4 : (c + (1 - β * (c - 1))) * u ≤ (c ^ 2 - 1) * u := by
          apply mul_le_mul_of_nonneg_right _ hu0
          linarith
        have e5 : (c ^ 2 - 1) * (d + l) ≤ c * d * c := by linarith
        have e6 : c * (c * d) ≤ c * ((c ^ 2 - 1) * u) :=
          mul_le_mul_of_nonneg_left (le_trans e3 e4) hc0.le
        have hpos : 0 < c ^ 2 - 1 := by nlinarith
        by_contra hcon
        push Not at hcon
        have := mul_lt_mul_of_pos_left hcon hpos
        linarith
    · have e1 : D + l ≤ u := le_trans hA2 hu1
      have g1 : β * (c - 1) * (D + l) ≤ β * (c - 1) * (c * M) :=
        mul_le_mul_of_nonneg_left hA2 hk
      have g2 : c * (x + β * (c - 1) * M) ≤ c * u := mul_le_mul_of_nonneg_left hu2x hc0.le
      have e2 : c * x + β * (c - 1) * (D + l) ≤ c * u := by linarith
      have h3 : (c - β * (c - 1)) * (D + l) ≤ (c - β * (c - 1)) * u :=
        mul_le_mul_of_nonneg_left e1 (by linarith)
      have h4 : 0 ≤ (c ^ 2 - 2 * c + β * (c - 1)) * u := mul_nonneg k2 hu0
      have e3 : c * (d + l) ≤ c * (c * u) := by
        have : c * (d + l) = c * x + c * (D + l) := by rw [hD]; ring
        rw [this]
        linarith
      exact le_of_mul_le_mul_left e3 hc0
  · rcases le_or_gt d b with hbd | hbd
    · apply le_trans (min_le_left _ _)
      rw [max_eq_left hbd]
      apply le_trans _ (le_max_left _ _)
      apply le_trans _ (le_max_left _ _)
      have := mul_nonneg hk hl'0
      linarith
    apply le_trans (min_le_right _ _)
    refine max_le (max_le ?_ ?_) ?_
    · apply le_trans _ (le_max_left _ _)
      apply le_trans _ (le_max_left _ _)
      have := mul_le_mul_of_nonneg_left hl1 hk
      linarith
    · apply le_trans _ (le_max_left _ _)
      apply le_trans _ (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left hl1 hc0.le
    rcases hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
    · by_contra hcon
      push Not at hcon
      have hN1 : X + β * (c - 1) * l' < (d + l) / c :=
        lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hcon
      have hN2 : c * l' < (d + l) / c :=
        lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hcon
      have hN3 : (u + l') / c < (d + l) / c := lt_of_le_of_lt (le_max_right _ _) hcon
      have g1 : c * (X + β * (c - 1) * l') < d + l := by
        rwa [lt_div_iff₀ hc0, mul_comm] at hN1
      have g2 : c * (c * l') < d + l := by
        rwa [lt_div_iff₀ hc0, mul_comm] at hN2
      have g3 : u + l' < d + l := by
        rwa [div_lt_div_iff_of_pos_right hc0] at hN3
      have ha : 0 < l - (c - 1) * D := by
        have := mul_le_mul_of_nonneg_left hA2 hc0.le
        linarith
      have hcc : 0 < D - (c - 1) * x - (c * β * (c - 1) - 1) * l := by
        have f1 : c * x ≤ c * X := mul_le_mul_of_nonneg_left hXx hc0.le
        have f2 : c * (β * (c - 1)) * l ≤ c * (β * (c - 1)) * l' :=
          mul_le_mul_of_nonneg_left hl1 (mul_nonneg hc0.le hk)
        linarith
      have hdd : 0 < x + D - (c ^ 2 - 1) * l := by
        have f1 : c * c * l ≤ c * c * l' := mul_le_mul_of_nonneg_left hl1 (by positivity)
        linarith
      have s1 := mul_nonneg k5 ha.le
      have s2 := mul_nonneg hc1 hdd.le
      have s3 : (2 * c - 1) * D ≤ (c - 1) ^ 2 * (c ^ 2 + c * β - 1) * D :=
        mul_le_mul_of_nonneg_right k4 hD0
      have hS : (c * β * (c - 1) - 1 + (c ^ 2 - 1) * (c - 1)) * (l - (c - 1) * D) +
          (D - (c - 1) * x - (c * β * (c - 1) - 1) * l) + (c - 1) * (x + D - (c ^ 2 - 1) * l) =
          (2 * c - 1) * D - (c - 1) ^ 2 * (c ^ 2 + c * β - 1) * D := by ring
      linarith
    · apply le_trans _ (le_max_right _ _)
      rw [div_le_div_iff_of_pos_right hc0]
      linarith

theorem psiB_step {c β b d l x M u l' X : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hcub : (1 - β) * (c - 1) ^ 2 ≤ cub c)
    (hl : 0 ≤ l) (hx : 0 ≤ x) (hxd : x ≤ d) (hXx : x ≤ X) (hXb : b ≤ X)
    (hM : PsiB c β l (d - x) l ≤ M) (hu1 : c * M ≤ u) (hu2 : X + β * (c - 1) * M ≤ u)
    (hl1 : l ≤ l') (hl2 : x + c * M ≤ u + l') : PsiB c β b d l ≤ PsiB c β X u l' := by
  have hk : 0 ≤ β * (c - 1) := mul_nonneg hβ0 (by linarith)
  have hMl : l ≤ M := le_trans (psiB_diag_ge (by linarith) hl) hM
  have := mul_le_mul_of_nonneg_left hMl hk
  exact psiB_step_gen hc hc2 hβ0 hβ1 hcub hl hx hxd hXx hXb hM hu1 (by linarith) (by linarith)
    hl1 hl2

inductive LStepB (c β : ℝ) : LLine → LLine → Prop
  | init (a l : ℝ) : LStepB c β ([], a, l) ([(0, 0, 0)], a, l)
  | speed (bs : List LBlock) (b xc lc a l x b₁ b₂ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₁ : max x b ≤ b₁) (h₂ : l ≤ b₂) (h₃ : a - x ≤ a₂) :
      LStepB c β (bs ++ [(b, xc, lc)], a, l) (bs ++ [(b₁, xc, lc), (b₂, x, l)], a₂, l)
  | slow (bs : List LBlock) (b xc lc a l e l' : ℝ) (h₁ : c * max b a ≤ e)
      (h₂ : ltop bs + β * (c - 1) * max b a ≤ e) (h₃ : lc ≤ l') (h₄ : 0 ≤ l')
      (h₅ : xc + c * max b a ≤ e + l') : LStepB c β (bs ++ [(b, xc, lc)], a, l) (bs, e, l')
  | weak (bs bs' : List LBlock) (a a' l l' : ℝ) (hl : bs'.length = bs.length)
      (hle : ∀ i, lsup bs i ≤ lsup bs' i) (hcr : ∀ i, lcre bs' i = lcre bs i) (ha : a ≤ a')
      (hll : l ≤ l') : LStepB c β (bs, a, l) (bs', a', l')

def LRefutesB (c β : ℝ) (n : ℕ) (L : ℕ → LLine) : Prop :=
  1 ≤ n ∧ (L 0).1 = [] ∧ (L n).1 = [] ∧ 0 ≤ (L 0).2.1 ∧ 0 ≤ (L 0).2.2 ∧
    (L n).2.1 < (L 0).2.1 ∧ (∀ i < n, LStepB c β (L i) (L (i + 1))) ∧
    (∀ i, 0 < i → i < n → (L i).1 ≠ [])

theorem lstepB_inv {c β : ℝ} {L L' : LLine} (h : LStepB c β L L') :
    (L.1 = [] ∧ L'.1 = [(0, 0, 0)] ∧ L'.2 = L.2) ∨
    (∃ (bs : List LBlock) (b xc lc x b₁ b₂ : ℝ), 0 ≤ x ∧ x ≤ L.2.1 ∧ max x b ≤ b₁ ∧
      L.2.2 ≤ b₂ ∧ L.2.1 - x ≤ L'.2.1 ∧ L'.2.2 = L.2.2 ∧ L.1 = bs ++ [(b, xc, lc)] ∧
      L'.1 = bs ++ [(b₁, xc, lc), (b₂, x, L.2.2)]) ∨
    (∃ b xc lc : ℝ, L.1 = L'.1 ++ [(b, xc, lc)] ∧ c * max b L.2.1 ≤ L'.2.1 ∧
      ltop L'.1 + β * (c - 1) * max b L.2.1 ≤ L'.2.1 ∧ lc ≤ L'.2.2 ∧ 0 ≤ L'.2.2 ∧
      xc + c * max b L.2.1 ≤ L'.2.1 + L'.2.2) ∨
    (L'.1.length = L.1.length ∧ (∀ i, lsup L.1 i ≤ lsup L'.1 i) ∧
      (∀ i, lcre L'.1 i = lcre L.1 i) ∧ L.2.1 ≤ L'.2.1 ∧ L.2.2 ≤ L'.2.2) := by
  cases h with
  | init a l => exact Or.inl ⟨rfl, rfl, rfl⟩
  | speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact Or.inr (Or.inl ⟨bs, b, xc, lc, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, rfl, rfl, rfl⟩)
  | slow bs b xc lc a l e l' h₁ h₂ h₃ h₄ h₅ =>
    exact Or.inr (Or.inr (Or.inl ⟨b, xc, lc, rfl, h₁, h₂, h₃, h₄, h₅⟩))
  | weak bs bs' a a' l l' hl hle hcr ha hll =>
    exact Or.inr (Or.inr (Or.inr ⟨hl, hle, hcr, ha, hll⟩))

theorem lstepB_len {c β : ℝ} {L L' : LLine} (h : LStepB c β L L') :
    L'.1.length ≤ L.1.length + 1 ∧ L.1.length ≤ L'.1.length + 1 := by
  rcases lstepB_inv h with ⟨h1, h2, _⟩ | ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, -, h1, h2⟩ |
    ⟨b, xc, lc, h1, -⟩ | ⟨h1, -⟩
  · rw [h1, h2]; simp
  · rw [h1, h2]; simp
  · rw [h1]; simp only [List.length_append, List.length_singleton]; omega
  · omega

theorem lstepB_nonneg {c β : ℝ} (hc : 0 ≤ c) {L L' : LLine} (h : LStepB c β L L') (ha : 0 ≤ L.2.1)
    (hl : 0 ≤ L.2.2) : 0 ≤ L'.2.1 ∧ 0 ≤ L'.2.2 := by
  rcases lstepB_inv h with ⟨-, -, h3⟩ | ⟨bs, b, xc, lc, x, b₁, b₂, -, hxa, -, -, h3, h4, -, -⟩ |
    ⟨b, xc, lc, -, h3, -, -, h4, -⟩ | ⟨-, -, -, h3, h4⟩
  · rw [h3]; exact ⟨ha, hl⟩
  · exact ⟨by linarith, by rw [h4]; exact hl⟩
  · exact ⟨le_trans (mul_nonneg hc (le_trans ha (le_max_right _ _))) h3, h4⟩
  · exact ⟨by linarith, by linarith⟩


theorem lstepB_mono {c β : ℝ} {L L' : LLine} (h : LStepB c β L L') {i : ℕ} (hi : i < L.1.length)
    (hi' : i < L'.1.length) : lsup L.1 i ≤ lsup L'.1 i ∧ lcre L'.1 i = lcre L.1 i := by
  rcases lstepB_inv h with ⟨h1, -, -⟩ | ⟨bs, b, xc, lc, x, b₁, b₂, -, -, hb, -, -, -, h1, h2⟩ |
    ⟨b, xc, lc, h1, -⟩ | ⟨-, hle, hcr, -, -⟩
  · rw [h1] at hi; simp at hi
  · rw [h1] at hi ⊢
    rw [h2]
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i bs.length with hlt | hge
    · unfold lsup lcre
      rw [getD_app_lt hlt, getD_app_lt hlt]
      exact ⟨le_rfl, rfl⟩
    · have : i = bs.length := by omega
      subst this
      unfold lsup lcre
      rw [getD_app_len, getD_app_len]
      refine ⟨?_, rfl⟩
      simp only [List.getD_cons_zero]
      exact le_trans (le_max_right _ _) hb
  · rw [h1]
    unfold lsup lcre
    rw [getD_app_lt hi']
    exact ⟨le_rfl, rfl⟩
  · exact ⟨hle i, hcr i⟩


theorem lsegmentB {c β : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hcub : (1 - β) * (c - 1) ^ 2 ≤ cub c) (L : ℕ → LLine) :
    ∀ len p k : ℕ, (∀ i, p ≤ i → i < p + len → LStepB c β (L i) (L (i + 1))) →
      (∀ i, p ≤ i → i ≤ p + len → k + 1 ≤ (L i).1.length ∧ 0 ≤ (L i).2.1 ∧ 0 ≤ (L i).2.2) →
      (L p).1.length = k + 1 → (L (p + len)).1.length = k + 1 →
      PsiB c β (ltop (L p).1) (L p).2.1 (L p).2.2 ≤ max (ltop (L (p + len)).1) (L (p + len)).2.1 := by
  have hc1 : (1 : ℝ) ≤ c := by linarith
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
  intro p k hstep hdep hp hq
  rcases Nat.eq_zero_or_pos len with h0 | hlen
  · subst h0
    exact psiB_le_max
  have hs0 := hstep p le_rfl (by omega)
  rcases lstepB_inv hs0 with ⟨h1, -, -⟩ |
    ⟨bs, b, xc, lc, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, h₄, e0, e1⟩ | ⟨b, xc, lc, e0, -⟩ |
    ⟨hl, hle, -, ha, hll⟩
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
      have h2 := (lstepB_len hsA).2
      omega
    rcases lstepB_inv hsA with ⟨h1, -, -⟩ |
      ⟨bs', b', xc', lc', x', b₁', b₂', -, -, -, -, -, -, f0, f1⟩ |
      ⟨y, xc', lc', f0, hu1, hu2, hu3, hu4, hu5⟩ | ⟨f0, -⟩
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
      have htopA : ltop (L (p + 1)).1 = b₂ := by
        rw [e1, show bs ++ [(b₁, xc, lc), (b₂, x, (L p).2.2)] =
          (bs ++ [(b₁, xc, lc)]) ++ [(b₂, x, (L p).2.2)] by simp, ltop_app]
      have htopY : ltop (L (m0 - 1)).1 = y := by rw [f0, ltop_app]
      rw [htopA, htopY] at hA
      have hmono : ∀ j, j ≤ m0 - 1 - (p + 1) →
          lsup (L (p + 1)).1 k ≤ lsup (L (p + 1 + j)).1 k ∧
          lcre (L (p + 1 + j)).1 (k + 1) = lcre (L (p + 1)).1 (k + 1) := by
        intro j
        induction j with
        | zero => intro _; exact ⟨le_rfl, rfl⟩
        | succ j ihj =>
          intro hj
          rw [show p + 1 + (j + 1) = p + 1 + j + 1 by omega]
          have hs := hstep (p + 1 + j) (by omega) (by omega)
          have g1 := hmin (p + 1 + j) (by omega) (by omega)
          have g2 := hmin (p + 1 + j + 1) (by omega) (by omega)
          have m1 := lstepB_mono hs (i := k) (by omega) (by omega)
          have m2 := lstepB_mono hs (i := k + 1) (by omega) (by omega)
          obtain ⟨i1, i2⟩ := ihj (by omega)
          exact ⟨le_trans i1 m1.1, by rw [m2.2]; exact i2⟩
      obtain ⟨hXX, hcre⟩ := hmono (m0 - 1 - (p + 1)) le_rfl
      rw [show p + 1 + (m0 - 1 - (p + 1)) = m0 - 1 by omega] at hXX hcre
      have hX1 : lsup (L (p + 1)).1 k = b₁ := by
        unfold lsup; rw [e1, ← hbs, getD_app_len]; rfl
      have hC1 : lcre (L (p + 1)).1 (k + 1) = (x, (L p).2.2) := by
        unfold lcre
        rw [e1, show bs ++ [(b₁, xc, lc), (b₂, x, (L p).2.2)] =
          (bs ++ [(b₁, xc, lc)]) ++ [(b₂, x, (L p).2.2)] by simp]
        have : k + 1 = (bs ++ [(b₁, xc, lc)]).length := by simp [hbs]
        rw [this, getD_app_len]; rfl
      have hX2 : lsup (L (m0 - 1)).1 k = ltop (L m0).1 := by
        unfold lsup; rw [f0, getD_app_lt (by omega), ltop_eq hm3]; rfl
      have hC2 : lcre (L (m0 - 1)).1 (k + 1) = (xc', lc') := by
        unfold lcre; rw [f0, ← hm3, getD_app_len]; rfl
      rw [hX1, hX2] at hXX
      rw [hC1, hC2] at hcre
      obtain ⟨hxc, hlc⟩ := Prod.mk.inj hcre
      rw [hlc] at hu3
      rw [hxc] at hu5
      have hbtop : ltop (L p).1 = b := by rw [e0, ltop_app]
      rw [hbtop]
      have hl0 := (hdep p le_rfl (by omega)).2.2
      have hMA : PsiB c β (L p).2.2 ((L p).2.1 - x) (L p).2.2 ≤ max y (L (m0 - 1)).2.1 := by
        have hp1 : (L (p + 1)).2.2 = (L p).2.2 := h₄
        rw [hp1] at hA
        exact le_trans (psiB_mono hc1 hβ0 h₂ h₃ le_rfl) hA
      have hstepP := psiB_step (X := ltop (L m0).1) hc hc2 hβ0 hβ1 hcub hl0 hx hxa
        (le_trans (le_max_left _ _) (le_trans h₁ hXX))
        (le_trans (le_max_right _ _) (le_trans h₁ hXX)) hMA hu1 hu2 hu3 hu5
      exact le_trans hstepP hB
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
    have htop : ltop (L p).1 ≤ ltop (L (p + 1)).1 := by
      rw [ltop_eq hp, ltop_eq hl1]; exact hle k
    exact le_trans (psiB_mono hc1 hβ0 htop ha hll) hrest

theorem lnoB_refutation_core {c β : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hcub : (1 - β) * (c - 1) ^ 2 ≤ cub c) (n : ℕ)
    (L : ℕ → LLine) : ¬ LRefutesB c β n L := by
  rintro ⟨hn, h0, hN, ha, hl, hlt, hstep, hmid⟩
  have hc0 : (0 : ℝ) < c := by linarith
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).2.1 ∧ 0 ≤ (L i).2.2 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨ha, hl⟩
    | succ i ih =>
      intro hi
      obtain ⟨a1, a2⟩ := ih (by omega)
      exact lstepB_nonneg hc0.le (hstep i (by omega)) a1 a2
  rcases lstepB_inv (hstep 0 (by omega)) with ⟨-, h1, h2⟩ |
    ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, -, e0, -⟩ | ⟨b, xc, lc, e0, -⟩ | ⟨hl0, -, -, ha', -⟩
  · rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · have hsN := hstep (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega] at hsN
      have hmidN := hmid (n - 1) (by omega) (by omega)
      rcases lstepB_inv hsN with ⟨g1, -, -⟩ |
        ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, -, -, g1⟩ | ⟨y, xc, lc, g0, hu1, -⟩ | ⟨g1, -⟩
      · exact hmidN g1
      · rw [hN] at g1; simp at g1
      · have hlen1 : (L (n - 1)).1.length = 0 + 1 := by rw [g0, hN]; rfl
        have hseg := lsegmentB hc hc2 hβ0 hβ1 hcub L (n - 2) 1 0
          (fun i h1 h2 => hstep i (by omega))
          (fun i h1 h2 => ⟨by
            have := hmid i (by omega) (by omega)
            exact Nat.one_le_iff_ne_zero.mpr (fun h => this (List.length_eq_zero_iff.mp h)),
            (hnn i (by omega)).1, (hnn i (by omega)).2⟩)
          (by rw [h1]; rfl) (by rw [show 1 + (n - 2) = n - 1 by omega]; exact hlen1)
        rw [show 1 + (n - 2) = n - 1 by omega, h1, h2] at hseg
        have hy : ltop (L (n - 1)).1 = y := by rw [g0, ltop_app]
        rw [hy] at hseg
        have htop : (L 0).2.1 / c ≤ PsiB c β (ltop [(0, 0, 0)]) (L 0).2.1 (L 0).2.2 := by
          have : ltop [((0 : ℝ), (0 : ℝ), (0 : ℝ))] = 0 := by
            unfold ltop lsup; simp
          rw [this]; exact psiB_top (by linarith) ha hl
        have hmax := le_trans htop hseg
        have h3 : c * ((L 0).2.1 / c) ≤ c * max y (L (n - 1)).2.1 :=
          mul_le_mul_of_nonneg_left hmax hc0.le
        rw [mul_div_cancel₀ _ hc0.ne'] at h3
        linarith
      · rw [hN] at g1; simp at g1; exact hmidN (List.length_eq_zero_iff.mp g1.symm)
    · have : n = 1 := by omega
      subst this
      rw [h1] at hN; simp at hN
  · rw [h0] at e0; simp at e0
  · rw [h0] at e0; simp at e0
  · rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · exact hmid 1 (by omega) hn1 (List.length_eq_zero_iff.mp (by rw [hl0, h0]; rfl))
    · have : n = 1 := by omega
      subst this
      linarith

theorem lstepB_restrict {c c₀ β : ℝ} (hβ : 0 ≤ β) (hcc : c₀ ≤ c) {L L' : LLine}
    (h : LStepB c β L L') (ha : 0 ≤ L.2.1) : LStepB c₀ β L L' := by
  cases h with
  | init a l => exact LStepB.init a l
  | speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact LStepB.speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃
  | weak bs bs' a a' l l' hl hle hcr hha hll => exact LStepB.weak bs bs' a a' l l' hl hle hcr hha hll
  | slow bs b xc lc a l e l' h₁ h₂ h₃ h₄ h₅ =>
    have hM : 0 ≤ max b a := le_trans ha (le_max_right _ _)
    have k := mul_le_mul_of_nonneg_right hcc hM
    have k2 := mul_le_mul_of_nonneg_left k hβ
    exact LStepB.slow bs b xc lc a l e l' (by linarith) (by nlinarith) h₃ h₄ (by linarith)

theorem no_refutation_locB {c β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hc1 : 1 ≤ c)
    (hcub : (1 - β) * (c - 1) ^ 2 ≤ cub c) (n : ℕ) (L : ℕ → LLine) : ¬ LRefutesB c β n L := by
  rintro ⟨hn, h0, hN, ha, hl, hlt, hstep, hmid⟩
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hr : r7 ≤ c := (cub_nonneg_iff hc1).mp (le_trans (by positivity) hcub)
  have h95 : 9 / 5 ≤ c := le_trans nine_fifths_lt_r7.le hr
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).2.1 ∧ 0 ≤ (L i).2.2 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨ha, hl⟩
    | succ i ih =>
      intro hi
      obtain ⟨a1, a2⟩ := ih (by omega)
      exact lstepB_nonneg hc0 (hstep i (by omega)) a1 a2
  rcases le_total c 2 with hc2 | hc2
  · exact lnoB_refutation_core h95 hc2 hβ0 hβ1 hcub n L ⟨hn, h0, hN, ha, hl, hlt, hstep, hmid⟩
  · apply lnoB_refutation_core (c := 2) (by norm_num) le_rfl hβ0 hβ1 (by unfold cub; nlinarith) n L
    exact ⟨hn, h0, hN, ha, hl, hlt,
      fun i hi => lstepB_restrict hβ0 hc2 (hstep i hi) (hnn i hi.le).1, hmid⟩

noncomputable def lbHalfLines : ℕ → LLine
  | 0 => ([], (1 : ℝ), (0 : ℝ))
  | 1 => ([((0 : ℝ), (0 : ℝ), (0 : ℝ))], (1 : ℝ), (0 : ℝ))
  | 2 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), ((0 : ℝ), ((29 : ℝ) / 69), (0 : ℝ))], ((40 : ℝ) / 69), (0 : ℝ))
  | 3 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ)), ((0 : ℝ), ((27 : ℝ) / 100), (0 : ℝ))], ((2137 : ℝ) / 6900), (0 : ℝ))
  | 4 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ)), (((17 : ℝ) / 98), ((27 : ℝ) / 100), (0 : ℝ)), ((0 : ℝ), ((17 : ℝ) / 98), (0 : ℝ))], ((46063 : ℝ) / 338100), (0 : ℝ))
  | 5 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ)), (((17 : ℝ) / 98), ((27 : ℝ) / 100), (0 : ℝ))], ((270764881 : ℝ) / 912870000), ((10 : ℝ) / 81))
  | 6 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ)), (((17 : ℝ) / 98), ((27 : ℝ) / 100), (0 : ℝ)), (((10 : ℝ) / 81), ((17 : ℝ) / 98), ((10 : ℝ) / 81))], ((112409881 : ℝ) / 912870000), ((10 : ℝ) / 81))
  | 7 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ)), (((17 : ℝ) / 98), ((27 : ℝ) / 100), (0 : ℝ))], ((219 : ℝ) / 980), ((17 : ℝ) / 98))
  | 8 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ))], ((614287 : ℝ) / 1274000), ((5 : ℝ) / 26))
  | 9 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ)), (((5 : ℝ) / 26), ((27 : ℝ) / 100), ((5 : ℝ) / 26))], ((270307 : ℝ) / 1274000), ((5 : ℝ) / 26))
  | 10 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ))], ((58823567 : ℝ) / 127400000), ((5 : ℝ) / 26))
  | 11 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ)), (((5 : ℝ) / 26), ((27 : ℝ) / 100), ((5 : ℝ) / 26))], ((24425567 : ℝ) / 127400000), ((5 : ℝ) / 26))
  | 12 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ))], ((181 : ℝ) / 520), ((27 : ℝ) / 100))
  | 13 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ))], ((261493373 : ℝ) / 348036000), ((29 : ℝ) / 97))
  | 14 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((29 : ℝ) / 97), ((29 : ℝ) / 69), ((29 : ℝ) / 97))], ((1669817 : ℝ) / 5044000), ((29 : ℝ) / 97))
  | 15 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ))], ((25076744513 : ℝ) / 34803600000), ((29 : ℝ) / 97))
  | 16 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((29 : ℝ) / 97), ((29 : ℝ) / 69), ((29 : ℝ) / 97))], ((151436877 : ℝ) / 504400000), ((29 : ℝ) / 97))
  | 17 => ([(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ))], ((27410074737 : ℝ) / 50440000000), ((29 : ℝ) / 69))
  | _ => ([], ((4961223527397 : ℝ) / 5044000000000), (0 : ℝ))

theorem lbHalf_refutes : LRefutesB ((181 : ℝ) / 100) ((1 : ℝ) / 2) 18 lbHalfLines := by
  refine ⟨by norm_num, rfl, rfl, by norm_num [lbHalfLines], by norm_num [lbHalfLines],
    by norm_num [lbHalfLines], ?_, ?_⟩
  · intro i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    · exact LStepB.init (1 : ℝ) (0 : ℝ)
    · have h := LStepB.speed (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [] (0 : ℝ) (0 : ℝ) (0 : ℝ) (1 : ℝ) (0 : ℝ) ((29 : ℝ) / 69) ((29 : ℝ) / 69) (0 : ℝ) ((40 : ℝ) / 69)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.speed (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ))] (0 : ℝ) ((29 : ℝ) / 69) (0 : ℝ) ((40 : ℝ) / 69) (0 : ℝ) ((27 : ℝ) / 100) ((27 : ℝ) / 100) (0 : ℝ) ((2137 : ℝ) / 6900)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.speed (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ))] (0 : ℝ) ((27 : ℝ) / 100) (0 : ℝ) ((2137 : ℝ) / 6900) (0 : ℝ) ((17 : ℝ) / 98) ((17 : ℝ) / 98) (0 : ℝ) ((46063 : ℝ) / 338100)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.slow (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ)), (((17 : ℝ) / 98), ((27 : ℝ) / 100), (0 : ℝ))] (0 : ℝ) ((17 : ℝ) / 98) (0 : ℝ) ((46063 : ℝ) / 338100) (0 : ℝ) ((270764881 : ℝ) / 912870000) ((10 : ℝ) / 81)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.speed (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ))] ((17 : ℝ) / 98) ((27 : ℝ) / 100) (0 : ℝ) ((270764881 : ℝ) / 912870000) ((10 : ℝ) / 81) ((17 : ℝ) / 98) ((17 : ℝ) / 98) ((10 : ℝ) / 81) ((112409881 : ℝ) / 912870000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.slow (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ)), (((17 : ℝ) / 98), ((27 : ℝ) / 100), (0 : ℝ))] ((10 : ℝ) / 81) ((17 : ℝ) / 98) ((10 : ℝ) / 81) ((112409881 : ℝ) / 912870000) ((10 : ℝ) / 81) ((219 : ℝ) / 980) ((17 : ℝ) / 98)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.slow (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ))] ((17 : ℝ) / 98) ((27 : ℝ) / 100) (0 : ℝ) ((219 : ℝ) / 980) ((17 : ℝ) / 98) ((614287 : ℝ) / 1274000) ((5 : ℝ) / 26)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.speed (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ))] ((27 : ℝ) / 100) ((29 : ℝ) / 69) (0 : ℝ) ((614287 : ℝ) / 1274000) ((5 : ℝ) / 26) ((27 : ℝ) / 100) ((27 : ℝ) / 100) ((5 : ℝ) / 26) ((270307 : ℝ) / 1274000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.slow (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ))] ((5 : ℝ) / 26) ((27 : ℝ) / 100) ((5 : ℝ) / 26) ((270307 : ℝ) / 1274000) ((5 : ℝ) / 26) ((58823567 : ℝ) / 127400000) ((5 : ℝ) / 26)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.speed (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ))] ((27 : ℝ) / 100) ((29 : ℝ) / 69) (0 : ℝ) ((58823567 : ℝ) / 127400000) ((5 : ℝ) / 26) ((27 : ℝ) / 100) ((27 : ℝ) / 100) ((5 : ℝ) / 26) ((24425567 : ℝ) / 127400000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.slow (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ)), (((27 : ℝ) / 100), ((29 : ℝ) / 69), (0 : ℝ))] ((5 : ℝ) / 26) ((27 : ℝ) / 100) ((5 : ℝ) / 26) ((24425567 : ℝ) / 127400000) ((5 : ℝ) / 26) ((181 : ℝ) / 520) ((27 : ℝ) / 100)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.slow (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ))] ((27 : ℝ) / 100) ((29 : ℝ) / 69) (0 : ℝ) ((181 : ℝ) / 520) ((27 : ℝ) / 100) ((261493373 : ℝ) / 348036000) ((29 : ℝ) / 97)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.speed (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [] ((29 : ℝ) / 69) (0 : ℝ) (0 : ℝ) ((261493373 : ℝ) / 348036000) ((29 : ℝ) / 97) ((29 : ℝ) / 69) ((29 : ℝ) / 69) ((29 : ℝ) / 97) ((1669817 : ℝ) / 5044000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.slow (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ))] ((29 : ℝ) / 97) ((29 : ℝ) / 69) ((29 : ℝ) / 97) ((1669817 : ℝ) / 5044000) ((29 : ℝ) / 97) ((25076744513 : ℝ) / 34803600000) ((29 : ℝ) / 97)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.speed (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [] ((29 : ℝ) / 69) (0 : ℝ) (0 : ℝ) ((25076744513 : ℝ) / 34803600000) ((29 : ℝ) / 97) ((29 : ℝ) / 69) ((29 : ℝ) / 69) ((29 : ℝ) / 97) ((151436877 : ℝ) / 504400000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.slow (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [(((29 : ℝ) / 69), (0 : ℝ), (0 : ℝ))] ((29 : ℝ) / 97) ((29 : ℝ) / 69) ((29 : ℝ) / 97) ((151436877 : ℝ) / 504400000) ((29 : ℝ) / 97) ((27410074737 : ℝ) / 50440000000) ((29 : ℝ) / 69)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStepB.slow (c := ((181 : ℝ) / 100)) (β := ((1 : ℝ) / 2)) [] ((29 : ℝ) / 69) (0 : ℝ) (0 : ℝ) ((27410074737 : ℝ) / 50440000000) ((29 : ℝ) / 69) ((4961223527397 : ℝ) / 5044000000000) (0 : ℝ)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · omega
  · intro i h1 h2
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    · omega
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · simp [lbHalfLines]
    · omega
    · omega

theorem r7_lt_181_100 : r7 < 181 / 100 := by
  have hpos : 0 < cub (181 / 100) := by unfold cub; norm_num
  rcases lt_or_ge r7 (181 / 100) with h | h
  · exact h
  · exfalso
    rcases eq_or_lt_of_le h with h' | h'
    · have := (cub_eq_zero_iff (by norm_num : (1 : ℝ) ≤ 181 / 100)).mpr h'
      linarith
    · have := (cub_neg_iff (by norm_num : (1 : ℝ) ≤ 181 / 100)).mpr h'
      linarith

theorem beta_half_beats_r7 :
    ∃ c : ℝ, r7 < c ∧ ∃ n L, LRefutesB c (1 / 2) n L :=
  ⟨181 / 100, r7_lt_181_100, 18, lbHalfLines, lbHalf_refutes⟩

theorem lstep_lstepB {c : ℝ} {L L' : LLine} (h : LStep c L L') : LStepB c 1 L L' := by
  cases h with
  | init a l => exact LStepB.init a l
  | speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact LStepB.speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃
  | slow bs b xc lc a l e l' h₁ h₂ h₃ h₄ h₅ =>
    exact LStepB.slow bs b xc lc a l e l' h₁ (by rw [one_mul]; exact h₂) h₃ h₄ h₅
  | weak bs bs' a a' l l' hl hle hcr hha hll => exact LStepB.weak bs bs' a a' l l' hl hle hcr hha hll

theorem no_refutation_loc_via_psiB {c : ℝ} (hc : r7 ≤ c) (n : ℕ) (L : ℕ → LLine) :
    ¬ LRefutes c n L := by
  rintro ⟨hn, h0, hN, ha, hl, hlt, hstep, hmid⟩
  have h1 := one_lt_r7
  have hcub : (1 - 1) * (c - 1) ^ 2 ≤ cub c := by
    rw [sub_self, zero_mul]; exact (cub_nonneg_iff (by linarith)).mpr hc
  exact no_refutation_locB (β := 1) (by norm_num) le_rfl (by linarith) hcub n L
    ⟨hn, h0, hN, ha, hl, hlt, fun i hi => lstep_lstepB (hstep i hi), hmid⟩

theorem psiB_step_sharp :
    ∃ b d l x M u l' X : ℝ, 0 ≤ l ∧ 0 ≤ x ∧ x ≤ d ∧ x ≤ X ∧ b ≤ X ∧
      PsiB (9 / 5) 1 l (d - x) l ≤ M ∧ 9 / 5 * M ≤ u ∧ X + 1 * (9 / 5 - 1) * M ≤ u ∧ l ≤ l' ∧
      x + 9 / 5 * M ≤ u + l' ∧ PsiB (9 / 5) 1 X u l' < PsiB (9 / 5) 1 b d l ∧ cub (9 / 5) < 0 := by
  refine ⟨0, 1, 45 / 101, 45 / 101, 56 / 101, 504 / 505, 45 / 101, 45 / 101, ?_⟩
  norm_num [PsiB, cub, max_def, min_def]

theorem psiB_step_sharp_half :
    ∃ b d l x M u l' X : ℝ, 0 ≤ l ∧ 0 ≤ x ∧ x ≤ d ∧ x ≤ X ∧ b ≤ X ∧
      PsiB (47 / 25) (1 / 2) l (d - x) l ≤ M ∧ 47 / 25 * M ≤ u ∧
      X + 1 / 2 * (47 / 25 - 1) * M ≤ u ∧ l ≤ l' ∧ x + 47 / 25 * M ≤ u + l' ∧
      PsiB (47 / 25) (1 / 2) X u l' < PsiB (47 / 25) (1 / 2) b d l ∧
      cub (47 / 25) < (1 - 1 / 2) * (47 / 25 - 1) ^ 2 := by
  refine ⟨0, 1, 38 / 97, 53 / 94, 41 / 94, 113072 / 113975, 38 / 97, 53 / 94, ?_⟩
  norm_num [PsiB, cub, max_def, min_def]

end PastaMath.SatBarriers
