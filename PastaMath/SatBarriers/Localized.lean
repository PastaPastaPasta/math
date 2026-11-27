-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Derivation

namespace PastaMath.SatBarriers

noncomputable def Psi (c b d l : ℝ) : ℝ := min (max b d) (max (b + (c - 1) * l) ((d + l) / c))

theorem nine_fifths_lt_r7 : 9 / 5 < r7 := by
  have h : cub (9 / 5) < 0 := by unfold cub; norm_num
  exact (cub_neg_iff (by norm_num)).mp h

theorem psi_mono {c b d l b' d' l' : ℝ} (hc : 1 ≤ c) (hb : b ≤ b') (hd : d ≤ d') (hl : l ≤ l') :
    Psi c b d l ≤ Psi c b' d' l' := by
  unfold Psi
  have hc0 : 0 < c := by linarith
  apply min_le_min (max_le_max hb hd)
  apply max_le_max
  · nlinarith
  · exact div_le_div_of_nonneg_right (by linarith) hc0.le

theorem psi_le_max {c b d l : ℝ} : Psi c b d l ≤ max b d := min_le_left _ _

theorem psi_diag_ge {c l D : ℝ} (hc : 1 ≤ c) (hl : 0 ≤ l) : l ≤ Psi c l D l := by
  unfold Psi
  apply le_min (le_max_left _ _)
  apply le_trans _ (le_max_left _ _)
  nlinarith

theorem psi_top {c a l : ℝ} (hc : 1 ≤ c) (ha : 0 ≤ a) (hl : 0 ≤ l) : a / c ≤ Psi c 0 a l := by
  unfold Psi
  have hc0 : 0 < c := by linarith
  apply le_min
  · rw [div_le_iff₀ hc0]; simp only [max_eq_right ha]; nlinarith
  · apply le_trans _ (le_max_right _ _)
    exact div_le_div_of_nonneg_right (by linarith) hc0.le

theorem ar_contra1 {c D l x : ℝ} (hc1 : 0 ≤ c - 1) (hphi : 0 ≤ c ^ 2 - c - 1)
    (hcubv : 1 ≤ (c - 1) * (c ^ 2 - 2)) (hD0 : 0 ≤ D) (ha : 0 < l - (c - 1) * D)
    (hb : 0 < x - (c - 1) * D) (hcc : 0 < D - (c ^ 2 - c - 1) * l - (c - 1) * x) : False := by
  nlinarith [mul_nonneg hc1 hb.le, mul_nonneg hphi ha.le, mul_nonneg hD0 (sub_nonneg.mpr hcubv)]

theorem ar_contra2 {c D l x : ℝ} (hc0 : 0 ≤ c) (hc1 : 0 ≤ c - 1) (hq : 0 ≤ 2 * c ^ 2 - 3 * c - 1)
    (hl : 0 ≤ l) (hlD : D < l) (hb : 0 < x - (c * l - D))
    (hcc : 0 < D - (c ^ 2 - c - 1) * l - (c - 1) * x) : False := by
  nlinarith [mul_nonneg hc1 hb.le, mul_nonneg hc0 (sub_nonneg.mpr hlD.le), mul_nonneg hq hl]

theorem psi_step {c b d l x M u l' X : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hcub : 0 ≤ cub c)
    (hl : 0 ≤ l) (hx : 0 ≤ x) (hxd : x ≤ d) (hXx : x ≤ X) (hXb : b ≤ X)
    (hM : Psi c l (d - x) l ≤ M) (hu1 : c * M ≤ u) (hu2 : X + (c - 1) * M ≤ u)
    (hl1 : l ≤ l') (hl2 : x + c * M ≤ u + l') : Psi c b d l ≤ Psi c X u l' := by
  have hc0 : 0 < c := by linarith
  have hc1 : 0 ≤ c - 1 := by linarith
  have hphi : 0 ≤ c ^ 2 - c - 1 := by nlinarith
  have hq : 0 ≤ 2 * c ^ 2 - 3 * c - 1 := by nlinarith
  have hsq : 2 ≤ c ^ 2 - 2 + 2 * 1 := by nlinarith
  have hpp : 2 ≤ (c ^ 2 - 2) * (c ^ 2 - 1) := by nlinarith
  have hcubv : 1 ≤ (c - 1) * (c ^ 2 - 2) := by unfold cub at hcub; nlinarith
  have hl'0 : 0 ≤ l' := le_trans hl hl1
  set D := d - x with hD
  have hD0 : 0 ≤ D := by linarith
  have hMl : l ≤ M := le_trans (psi_diag_ge (by linarith) hl) hM
  have hA : (l ≤ M ∧ D ≤ M) ∨ (c * l ≤ M ∧ (D + l) / c ≤ M) := by
    unfold Psi at hM
    rcases min_le_iff.mp hM with h | h
    · exact Or.inl ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩
    · refine Or.inr ⟨le_trans ?_ (le_trans (le_max_left _ _) h), le_trans (le_max_right _ _) h⟩
      linarith
  have hfrac : ∀ z : ℝ, (d + l) / c ≤ z ↔ d + l ≤ c * z := fun z => by
    rw [div_le_iff₀ hc0, mul_comm]
  have hfrac' : ∀ z : ℝ, z ≤ (u + l') / c ↔ c * z ≤ u + l' := fun z => by
    rw [le_div_iff₀ hc0, mul_comm]
  unfold Psi
  apply le_min
  · apply le_trans _ (le_max_right X u)
    rcases le_or_gt d b with hbd | hbd
    · exact le_trans (min_le_left _ _) (by rw [max_eq_left hbd]; linarith [hu2, mul_nonneg hc1 (le_trans hl hMl)])
    apply le_trans (min_le_right _ _)
    rcases le_total ((d + l) / c) (b + (c - 1) * l) with hF | hF
    · rw [max_eq_left hF]
      have := mul_le_mul_of_nonneg_left hMl hc1
      linarith
    rw [max_eq_right hF, hfrac]
    rcases hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
    · rcases le_total d ((c ^ 2 - 1) * l) with hcl | hcl
      · have := mul_le_mul_of_nonneg_left hA1 hc0.le
        nlinarith
      · have e1 := mul_le_mul_of_nonneg_left hA2 hc0.le
        have e2 := mul_le_mul_of_nonneg_left hA2 hc1
        have e3 : 2 * u ≥ c * d := by
          have f1 : (2 - c) * (c * D) ≤ (2 - c) * u :=
            mul_le_mul_of_nonneg_left (le_trans e1 hu1) (by linarith)
          have f2 : c * (x + (c - 1) * D) ≤ c * u :=
            mul_le_mul_of_nonneg_left (by linarith) hc0.le
          nlinarith
        have e4 : (c ^ 2 - 2) * ((c ^ 2 - 1) * l) ≤ (c ^ 2 - 2) * d :=
          mul_le_mul_of_nonneg_left hcl (by nlinarith)
        have e5 : 2 * l ≤ (c ^ 2 - 2) * ((c ^ 2 - 1) * l) := by nlinarith
        have e6 : c * (c * d) ≤ c * (2 * u) := mul_le_mul_of_nonneg_left e3 hc0.le
        nlinarith
    · have e1 : D + l ≤ c * M := by rwa [div_le_iff₀ hc0, mul_comm] at hA2
      have e2 : (c - 1) * (D + l) ≤ c * ((c - 1) * M) := by nlinarith
      have e3 : c * (x + (c - 1) * M) ≤ c * u := mul_le_mul_of_nonneg_left (by linarith) hc0.le
      have e4 : (c + 1) * u ≥ c * (d + l) := by nlinarith
      have e5 : 0 ≤ d + l := by linarith
      have e6 : (c + 1) * (d + l) ≤ c * (c * (d + l)) := by nlinarith
      have e7 : (c + 1) * (d + l) ≤ (c + 1) * (c * u) := by nlinarith
      exact le_of_mul_le_mul_left e7 (by linarith)
  · rcases le_or_gt d b with hbd | hbd
    · apply le_trans (min_le_left _ _)
      rw [max_eq_left hbd]
      apply le_trans _ (le_max_left _ _)
      have := mul_nonneg hc1 hl'0
      linarith
    apply le_trans (min_le_right _ _)
    rcases le_total ((d + l) / c) (b + (c - 1) * l) with hF | hF
    · rw [max_eq_left hF]
      apply le_trans _ (le_max_left _ _)
      have := mul_le_mul_of_nonneg_left hl1 hc1
      linarith
    rw [max_eq_right hF]
    rcases hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
    · by_contra hcon
      push Not at hcon
      have hT1 : X + (c - 1) * l' < (d + l) / c := lt_of_le_of_lt (le_max_left _ _) hcon
      have hT2 : (u + l') / c < (d + l) / c := lt_of_le_of_lt (le_max_right _ _) hcon
      have g2 : u + l' < d + l := by
        rwa [div_lt_div_iff_of_pos_right hc0] at hT2
      have g1 : c * (X + (c - 1) * l') < d + l := by
        rwa [lt_div_iff₀ hc0, mul_comm] at hT1
      have e4 : c * (X + (c - 1) * l') = c * X + c * (c - 1) * l' := by ring
      have f1 : c * x ≤ c * X := mul_le_mul_of_nonneg_left hXx hc0.le
      have f2 : c * (c - 1) * l ≤ c * (c - 1) * l' :=
        mul_le_mul_of_nonneg_left hl1 (mul_nonneg hc0.le hc1)
      have e1 : (c - 1) * D = c * D - D := by ring
      have e2 : (c ^ 2 - c - 1) * l = c * (c - 1) * l - l := by ring
      have e3 : (c - 1) * x = c * x - x := by ring
      have hcc : 0 < D - (c ^ 2 - c - 1) * l - (c - 1) * x := by linarith
      rcases le_or_gt l D with hlD | hlD
      · have a1 : c * D ≤ c * M := mul_le_mul_of_nonneg_left hA2 hc0.le
        have ha : 0 < l - (c - 1) * D := by linarith
        have hb : 0 < x - (c - 1) * D := by linarith
        exact ar_contra1 hc1 hphi hcubv hD0 ha hb hcc
      · have a1 : c * l ≤ c * M := mul_le_mul_of_nonneg_left hA1 hc0.le
        have hb : 0 < x - (c * l - D) := by linarith
        exact ar_contra2 hc0.le hc1 hq hl hlD hb hcc
    · apply le_trans _ (le_max_right _ _)
      rw [div_le_div_iff_of_pos_right hc0]
      have e1 : D + l ≤ c * M := by rwa [div_le_iff₀ hc0, mul_comm] at hA2
      linarith

abbrev LBlock := ℝ × ℝ × ℝ

abbrev LLine := List LBlock × ℝ × ℝ

def lsup (l : List LBlock) (i : ℕ) : ℝ := (l.getD i (0, 0, 0)).1

def lcre (l : List LBlock) (i : ℕ) : ℝ × ℝ := (l.getD i (0, 0, 0)).2

def ltop (l : List LBlock) : ℝ := lsup l (l.length - 1)

inductive LStep (c : ℝ) : LLine → LLine → Prop
  | init (a l : ℝ) : LStep c ([], a, l) ([(0, 0, 0)], a, l)
  | speed (bs : List LBlock) (b xc lc a l x b₁ b₂ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₁ : max x b ≤ b₁) (h₂ : l ≤ b₂) (h₃ : a - x ≤ a₂) :
      LStep c (bs ++ [(b, xc, lc)], a, l) (bs ++ [(b₁, xc, lc), (b₂, x, l)], a₂, l)
  | slow (bs : List LBlock) (b xc lc a l e l' : ℝ) (h₁ : c * max b a ≤ e)
      (h₂ : ltop bs + (c - 1) * max b a ≤ e) (h₃ : lc ≤ l') (h₄ : 0 ≤ l')
      (h₅ : xc + c * max b a ≤ e + l') : LStep c (bs ++ [(b, xc, lc)], a, l) (bs, e, l')
  | weak (bs bs' : List LBlock) (a a' l l' : ℝ) (hl : bs'.length = bs.length)
      (hle : ∀ i, lsup bs i ≤ lsup bs' i) (hcr : ∀ i, lcre bs' i = lcre bs i) (ha : a ≤ a')
      (hll : l ≤ l') : LStep c (bs, a, l) (bs', a', l')

def LRefutes (c : ℝ) (n : ℕ) (L : ℕ → LLine) : Prop :=
  1 ≤ n ∧ (L 0).1 = [] ∧ (L n).1 = [] ∧ 0 ≤ (L 0).2.1 ∧ 0 ≤ (L 0).2.2 ∧
    (L n).2.1 < (L 0).2.1 ∧ (∀ i < n, LStep c (L i) (L (i + 1))) ∧
    (∀ i, 0 < i → i < n → (L i).1 ≠ [])

theorem lstep_inv {c : ℝ} {L L' : LLine} (h : LStep c L L') :
    (L.1 = [] ∧ L'.1 = [(0, 0, 0)] ∧ L'.2 = L.2) ∨
    (∃ (bs : List LBlock) (b xc lc x b₁ b₂ : ℝ), 0 ≤ x ∧ x ≤ L.2.1 ∧ max x b ≤ b₁ ∧
      L.2.2 ≤ b₂ ∧ L.2.1 - x ≤ L'.2.1 ∧ L'.2.2 = L.2.2 ∧ L.1 = bs ++ [(b, xc, lc)] ∧
      L'.1 = bs ++ [(b₁, xc, lc), (b₂, x, L.2.2)]) ∨
    (∃ b xc lc : ℝ, L.1 = L'.1 ++ [(b, xc, lc)] ∧ c * max b L.2.1 ≤ L'.2.1 ∧
      ltop L'.1 + (c - 1) * max b L.2.1 ≤ L'.2.1 ∧ lc ≤ L'.2.2 ∧ 0 ≤ L'.2.2 ∧
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

theorem lstep_len {c : ℝ} {L L' : LLine} (h : LStep c L L') :
    L'.1.length ≤ L.1.length + 1 ∧ L.1.length ≤ L'.1.length + 1 := by
  rcases lstep_inv h with ⟨h1, h2, _⟩ | ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, -, h1, h2⟩ |
    ⟨b, xc, lc, h1, -⟩ | ⟨h1, -⟩
  · rw [h1, h2]; simp
  · rw [h1, h2]; simp
  · rw [h1]; simp only [List.length_append, List.length_singleton]; omega
  · omega

theorem lstep_nonneg {c : ℝ} (hc : 0 ≤ c) {L L' : LLine} (h : LStep c L L') (ha : 0 ≤ L.2.1)
    (hl : 0 ≤ L.2.2) : 0 ≤ L'.2.1 ∧ 0 ≤ L'.2.2 := by
  rcases lstep_inv h with ⟨-, -, h3⟩ | ⟨bs, b, xc, lc, x, b₁, b₂, -, hxa, -, -, h3, h4, -, -⟩ |
    ⟨b, xc, lc, -, h3, -, -, h4, -⟩ | ⟨-, -, -, h3, h4⟩
  · rw [h3]; exact ⟨ha, hl⟩
  · exact ⟨by linarith, by rw [h4]; exact hl⟩
  · exact ⟨le_trans (mul_nonneg hc (le_trans ha (le_max_right _ _))) h3, h4⟩
  · exact ⟨by linarith, by linarith⟩

theorem getD_app_lt {l₁ l₂ : List LBlock} {i : ℕ} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i (0, 0, 0) = l₁.getD i (0, 0, 0) := List.getD_append _ _ _ _ h

theorem getD_app_len (l₁ l₂ : List LBlock) :
    (l₁ ++ l₂).getD l₁.length (0, 0, 0) = l₂.getD 0 (0, 0, 0) := by
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]

theorem lstep_mono {c : ℝ} {L L' : LLine} (h : LStep c L L') {i : ℕ} (hi : i < L.1.length)
    (hi' : i < L'.1.length) : lsup L.1 i ≤ lsup L'.1 i ∧ lcre L'.1 i = lcre L.1 i := by
  rcases lstep_inv h with ⟨h1, -, -⟩ | ⟨bs, b, xc, lc, x, b₁, b₂, -, -, hb, -, -, -, h1, h2⟩ |
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

theorem ltop_app (bs : List LBlock) (blk : LBlock) : ltop (bs ++ [blk]) = blk.1 := by
  unfold ltop lsup
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, getD_app_len]
  rfl

theorem ltop_eq {l : List LBlock} {k : ℕ} (h : l.length = k + 1) : ltop l = lsup l k := by
  unfold ltop; rw [h, Nat.add_sub_cancel]

theorem lsegment {c : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hcub : 0 ≤ cub c) (L : ℕ → LLine) :
    ∀ len p k : ℕ, (∀ i, p ≤ i → i < p + len → LStep c (L i) (L (i + 1))) →
      (∀ i, p ≤ i → i ≤ p + len → k + 1 ≤ (L i).1.length ∧ 0 ≤ (L i).2.1 ∧ 0 ≤ (L i).2.2) →
      (L p).1.length = k + 1 → (L (p + len)).1.length = k + 1 →
      Psi c (ltop (L p).1) (L p).2.1 (L p).2.2 ≤ max (ltop (L (p + len)).1) (L (p + len)).2.1 := by
  have hc1 : (1 : ℝ) ≤ c := by linarith
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
  intro p k hstep hdep hp hq
  rcases Nat.eq_zero_or_pos len with h0 | hlen
  · subst h0
    exact psi_le_max
  have hs0 := hstep p le_rfl (by omega)
  rcases lstep_inv hs0 with ⟨h1, -, -⟩ |
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
      have h2 := (lstep_len hsA).2
      omega
    rcases lstep_inv hsA with ⟨h1, -, -⟩ |
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
          have m1 := lstep_mono hs (i := k) (by omega) (by omega)
          have m2 := lstep_mono hs (i := k + 1) (by omega) (by omega)
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
      have hMA : Psi c (L p).2.2 ((L p).2.1 - x) (L p).2.2 ≤ max y (L (m0 - 1)).2.1 := by
        have hp1 : (L (p + 1)).2.2 = (L p).2.2 := h₄
        rw [hp1] at hA
        exact le_trans (psi_mono hc1 h₂ h₃ le_rfl) hA
      have hstepP := psi_step (X := ltop (L m0).1) hc hc2 hcub hl0 hx hxa
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
    exact le_trans (psi_mono hc1 htop ha hll) hrest

theorem lno_refutation_core {c : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hcub : 0 ≤ cub c) (n : ℕ)
    (L : ℕ → LLine) : ¬ LRefutes c n L := by
  rintro ⟨hn, h0, hN, ha, hl, hlt, hstep, hmid⟩
  have hc0 : (0 : ℝ) < c := by linarith
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).2.1 ∧ 0 ≤ (L i).2.2 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨ha, hl⟩
    | succ i ih =>
      intro hi
      obtain ⟨a1, a2⟩ := ih (by omega)
      exact lstep_nonneg hc0.le (hstep i (by omega)) a1 a2
  rcases lstep_inv (hstep 0 (by omega)) with ⟨-, h1, h2⟩ |
    ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, -, e0, -⟩ | ⟨b, xc, lc, e0, -⟩ | ⟨hl0, -, -, ha', -⟩
  · rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · have hsN := hstep (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega] at hsN
      have hmidN := hmid (n - 1) (by omega) (by omega)
      rcases lstep_inv hsN with ⟨g1, -, -⟩ |
        ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, -, -, g1⟩ | ⟨y, xc, lc, g0, hu1, -⟩ | ⟨g1, -⟩
      · exact hmidN g1
      · rw [hN] at g1; simp at g1
      · have hlen1 : (L (n - 1)).1.length = 0 + 1 := by rw [g0, hN]; rfl
        have hseg := lsegment hc hc2 hcub L (n - 2) 1 0
          (fun i h1 h2 => hstep i (by omega))
          (fun i h1 h2 => ⟨by
            have := hmid i (by omega) (by omega)
            exact Nat.one_le_iff_ne_zero.mpr (fun h => this (List.length_eq_zero_iff.mp h)),
            (hnn i (by omega)).1, (hnn i (by omega)).2⟩)
          (by rw [h1]; rfl) (by rw [show 1 + (n - 2) = n - 1 by omega]; exact hlen1)
        rw [show 1 + (n - 2) = n - 1 by omega, h1, h2] at hseg
        have hy : ltop (L (n - 1)).1 = y := by rw [g0, ltop_app]
        rw [hy] at hseg
        have htop : (L 0).2.1 / c ≤ Psi c (ltop [(0, 0, 0)]) (L 0).2.1 (L 0).2.2 := by
          have : ltop [((0 : ℝ), (0 : ℝ), (0 : ℝ))] = 0 := by
            unfold ltop lsup; simp
          rw [this]; exact psi_top (by linarith) ha hl
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

theorem lstep_restrict {c c₀ : ℝ} (hcc : c₀ ≤ c) {L L' : LLine}
    (h : LStep c L L') (ha : 0 ≤ L.2.1) : LStep c₀ L L' := by
  cases h with
  | init a l => exact LStep.init a l
  | speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact LStep.speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃
  | weak bs bs' a a' l l' hl hle hcr hha hll => exact LStep.weak bs bs' a a' l l' hl hle hcr hha hll
  | slow bs b xc lc a l e l' h₁ h₂ h₃ h₄ h₅ =>
    have hM : 0 ≤ max b a := le_trans ha (le_max_right _ _)
    have k := mul_le_mul_of_nonneg_right hcc hM
    exact LStep.slow bs b xc lc a l e l' (by linarith) (by linarith) h₃ h₄ (by linarith)

theorem no_refutation_loc {c : ℝ} (hc : r7 ≤ c) (n : ℕ) (L : ℕ → LLine) :
    ¬ LRefutes c n L := by
  rintro ⟨hn, h0, hN, ha, hl, hlt, hstep, hmid⟩
  have h1 := one_lt_r7
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).2.1 ∧ 0 ≤ (L i).2.2 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨ha, hl⟩
    | succ i ih =>
      intro hi
      obtain ⟨a1, a2⟩ := ih (by omega)
      exact lstep_nonneg hc0 (hstep i (by omega)) a1 a2
  apply lno_refutation_core (c := r7) nine_fifths_lt_r7.le r7_lt_two.le (le_of_eq cub_r7.symm) n L
  exact ⟨hn, h0, hN, ha, hl, hlt,
    fun i hi => lstep_restrict hc (hstep i hi) (hnn i hi.le).1, hmid⟩

noncomputable def lvLLines : ℕ → LLine
  | 0 => ([], 1, 0)
  | 1 => ([(0, 0, 0)], 1, 0)
  | 2 => ([(1 / 2, 0, 0), (0, 1 / 2, 0)], 1 / 2, 0)
  | 3 => ([(1 / 2, 0, 0)], 7 / 10, 1 / 2)
  | _ => ([], 49 / 50, 0)

theorem lv_lrefutation : LRefutes (7 / 5) 4 lvLLines := by
  refine ⟨by norm_num, rfl, rfl, by norm_num [lvLLines], by norm_num [lvLLines],
    by norm_num [lvLLines], ?_, ?_⟩
  · intro i hi
    rcases i with _ | _ | _ | _ | i
    · exact LStep.init 1 0
    · have h := LStep.speed (c := 7 / 5) [] 0 0 0 1 0 (1 / 2) (1 / 2) 0 (1 / 2)
        (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
      exact h
    · have h := LStep.slow (c := 7 / 5) [(1 / 2, 0, 0)] 0 (1 / 2) 0 (1 / 2) 0 (7 / 10) (1 / 2)
        (by norm_num) (by norm_num [ltop, lsup]) (by norm_num) (by norm_num) (by norm_num)
      exact h
    · have h := LStep.slow (c := 7 / 5) [] (1 / 2) 0 0 (7 / 10) (1 / 2) (49 / 50) 0
        (by norm_num) (by norm_num [ltop, lsup]) le_rfl le_rfl (by norm_num)
      exact h
    · omega
  · intro i h1 h2
    rcases i with _ | _ | _ | _ | i
    · omega
    · simp [lvLLines]
    · simp [lvLLines]
    · simp [lvLLines]
    · omega

theorem lstep_localized_witness (c : ℝ) :
    LStep c ([(1, 0, 0)], 1, 0) ([(1, 0, 0), (0, 1 / 2, 0)], 1 / 2, 0) := by
  have h := LStep.speed (c := c) [] 1 0 0 1 0 (1 / 2) 1 0 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by norm_num)
  exact h

def Emb (R : RLine) (L : LLine) : Prop :=
  L.1.map Prod.fst = R.1 ∧ L.2.1 = R.2 ∧ 0 ≤ L.2.2 ∧ L.2.2 ≤ ltop L.1 ∧
    (∀ j, 0 ≤ lsup L.1 j) ∧
    (∀ j, (lcre L.1 (j + 1)).1 ≤ lsup L.1 j ∧ (lcre L.1 (j + 1)).2 ≤ lsup L.1 j) ∧
    (lcre L.1 0).1 ≤ 0 ∧ (lcre L.1 0).2 ≤ 0

theorem getD_map_fst (l : List LBlock) (j : ℕ) : (l.map Prod.fst).getD j 0 = lsup l j := by
  unfold lsup
  rw [show (0 : ℝ) = Prod.fst ((0 : ℝ), (0 : ℝ), (0 : ℝ)) from rfl, List.getD_map]

theorem top_map_fst (l : List LBlock) : top (l.map Prod.fst) = ltop l := by
  unfold top ltop; rw [List.length_map, getD_map_fst]

theorem getD_zip_parts (l₁ : List ℝ) (l₂ : List (ℝ × ℝ)) (h : l₁.length = l₂.length) (j : ℕ) :
    ((l₁.zip l₂).getD j (0, 0, 0)).1 = l₁.getD j 0 ∧
      ((l₁.zip l₂).getD j (0, 0, 0)).2 = l₂.getD j (0, 0) := by
  rcases Nat.lt_or_ge j l₁.length with hj | hj
  · have hj2 : j < l₂.length := by omega
    have hz : j < (l₁.zip l₂).length := by rw [List.length_zip]; omega
    rw [List.getD_eq_getElem _ _ hz, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj2,
      List.getElem_zip]
    exact ⟨rfl, rfl⟩
  · have hz : (l₁.zip l₂).length ≤ j := by rw [List.length_zip]; omega
    rw [List.getD_eq_default _ _ hz, List.getD_eq_default _ _ hj,
      List.getD_eq_default _ _ (by omega)]
    exact ⟨rfl, rfl⟩

theorem snoc_of_map {l : List LBlock} {bs : List ℝ} {b : ℝ} (h : l.map Prod.fst = bs ++ [b]) :
    ∃ l₁ xc lc, l = l₁ ++ [(b, xc, lc)] ∧ l₁.map Prod.fst = bs := by
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.map_eq_append_iff.mp h
  obtain ⟨blk, rfl, hb⟩ : ∃ blk, l₂ = [blk] ∧ blk.1 = b := by
    rcases l₂ with _ | ⟨blk, _ | ⟨blk', t⟩⟩
    · simp at h2
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h2
      exact ⟨blk, rfl, h2⟩
    · simp at h2
  exact ⟨l₁, blk.2.1, blk.2.2, by rw [← hb], h1⟩

theorem getD_snoc1 (l₁ : List LBlock) (p : LBlock) (j : ℕ) :
    (l₁ ++ [p]).getD j (0, 0, 0) =
      if j < l₁.length then l₁.getD j (0, 0, 0) else if j = l₁.length then p else (0, 0, 0) := by
  split_ifs with h1 h2
  · exact getD_app_lt h1
  · subst h2; rw [getD_app_len]; rfl
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem getD_snoc2 (l₁ : List LBlock) (p q : LBlock) (j : ℕ) :
    (l₁ ++ [p, q]).getD j (0, 0, 0) =
      if j < l₁.length then l₁.getD j (0, 0, 0) else if j = l₁.length then p
      else if j = l₁.length + 1 then q else (0, 0, 0) := by
  have e : l₁ ++ [p, q] = (l₁ ++ [p]) ++ [q] := by simp
  rw [e, getD_snoc1, getD_snoc1]
  simp only [List.length_append, List.length_singleton]
  split_ifs <;> first | rfl | omega

theorem step_lift {c : ℝ} {R R' : RLine} {L : LLine} (h : Step c 1 R R')
    (hE : Emb R L) : ∃ L', LStep c L L' ∧ Emb R' L' := by
  obtain ⟨hm, ha, hl0, hlt, hsup, hcre, hc0, hc0'⟩ := hE
  obtain ⟨bL, aL, lL⟩ := L
  simp only at hm ha hl0 hlt hsup hcre hc0 hc0'
  cases h with
  | init a =>
    have hb : bL = [] := List.map_eq_nil_iff.mp hm
    subst hb
    have hl00 : lL = 0 := le_antisymm (by simpa [ltop, lsup] using hlt) hl0
    subst hl00
    refine ⟨([(0, 0, 0)], aL, 0), LStep.init aL 0, ?_⟩
    simp only at ha
    refine ⟨rfl, ha, le_rfl, by simp [ltop, lsup], ?_, ?_, by simp [lcre], by simp [lcre]⟩
    · intro j; rcases j with _ | j <;> simp [lsup]
    · intro j; rcases j with _ | j <;> simp [lcre, lsup]
  | speed bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    obtain ⟨l₁, xc, lc, rfl, hl₁⟩ := snoc_of_map hm
    simp only at ha
    have htopb : ltop (l₁ ++ [(b, xc, lc)]) = b := by rw [ltop_app]
    rw [htopb] at hlt
    have hb0 : 0 ≤ b := by
      have := hsup l₁.length; unfold lsup at this; rwa [getD_app_len] at this
    have hb1 : b ≤ b₁ := le_trans (le_max_right x b) h₁
    have hx1 : x ≤ b₁ := le_trans (le_max_left x b) h₁
    refine ⟨(l₁ ++ [(b₁, xc, lc), (b₂, x, lL)], a₂, lL),
      LStep.speed l₁ b xc lc aL lL x b₁ b₂ a₂ hx (by rw [ha]; exact hxa) h₁
        (by linarith) (by rw [ha]; exact h₃), ?_⟩
    have hsupn : ∀ j, 0 ≤ lsup (l₁ ++ [(b₁, xc, lc), (b₂, x, lL)]) j := by
      intro j
      have hj := hsup j
      unfold lsup at hj ⊢
      rw [getD_snoc2]; rw [getD_snoc1] at hj
      split_ifs at hj ⊢ <;> first | exact hj | (simp only; linarith)
    refine ⟨by simp [hl₁], rfl, hl0, ?_, hsupn, ?_, ?_, ?_⟩
    · have e2 : l₁ ++ [(b₁, xc, lc), (b₂, x, lL)] = (l₁ ++ [(b₁, xc, lc)]) ++ [(b₂, x, lL)] := by
        simp
      rw [e2, ltop_app]; simp only; linarith
    · intro j
      have hj := hcre j
      have hs := hsupn j
      unfold lcre lsup at hj hs ⊢
      rw [getD_snoc2, getD_snoc2]; rw [getD_snoc2] at hs; rw [getD_snoc1, getD_snoc1] at hj
      split_ifs at hj hs ⊢ <;>
        first | exact hj | exact ⟨hs, hs⟩ | (simp only; constructor <;> linarith) | omega
    · have hj := hc0
      unfold lcre at hj ⊢
      rw [getD_snoc2]; rw [getD_snoc1] at hj
      split_ifs at hj ⊢ <;> first | contradiction | exact hj
    · have hj := hc0'
      unfold lcre at hj ⊢
      rw [getD_snoc2]; rw [getD_snoc1] at hj
      split_ifs at hj ⊢ <;> first | contradiction | exact hj
  | slow bs b a e h₁ h₂ =>
    obtain ⟨l₁, xc, lc, rfl, hl₁⟩ := snoc_of_map hm
    simp only at ha
    rw [← ha] at h₁ h₂
    have htopR : top bs = ltop l₁ := by rw [← hl₁, top_map_fst]
    rw [htopR, one_mul] at h₂
    have hlast : xc ≤ ltop l₁ ∧ lc ≤ ltop l₁ := by
      rcases Nat.eq_zero_or_pos l₁.length with h0 | hpos
      · have : l₁ = [] := List.length_eq_zero_iff.mp h0
        subst this
        have e0 : ltop ([] : List LBlock) = 0 := by simp [ltop, lsup]
        rw [e0]
        have h1 := hc0
        have h2 := hc0'
        unfold lcre at h1 h2
        simp only [List.nil_append, List.getD_cons_zero] at h1 h2
        exact ⟨h1, h2⟩
      · have := hcre (l₁.length - 1)
        unfold lcre lsup at this
        rw [show l₁.length - 1 + 1 = l₁.length by omega, getD_app_len,
          getD_app_lt (by omega)] at this
        unfold ltop lsup
        exact this
    have hnn : 0 ≤ ltop l₁ := by
      unfold ltop
      have := hsup (l₁.length - 1)
      unfold lsup at this ⊢
      rcases Nat.eq_zero_or_pos l₁.length with h0 | hpos
      · rw [List.getD_eq_default _ _ (by omega)]
      · rwa [getD_app_lt (by omega)] at this
    refine ⟨(l₁, e, ltop l₁), LStep.slow l₁ b xc lc aL lL e (ltop l₁) h₁ h₂ hlast.2 hnn (by
      have := hlast.1; linarith), ?_⟩
    have hsupn : ∀ j, 0 ≤ lsup l₁ j := by
      intro j
      have hj := hsup j
      unfold lsup at hj ⊢
      rw [getD_snoc1] at hj
      split_ifs at hj with h1 h2
      · exact hj
      · rw [List.getD_eq_default _ _ (by omega)]
      · rw [List.getD_eq_default _ _ (by omega)]
    refine ⟨hl₁, rfl, hnn, le_rfl, hsupn, ?_, ?_, ?_⟩
    · intro j
      dsimp only
      have hj := hcre j
      have hs := hsupn j
      unfold lcre lsup at hj hs ⊢
      rw [getD_snoc1, getD_snoc1] at hj
      by_cases hj1 : j + 1 < l₁.length
      · rw [if_pos hj1, if_pos (by omega)] at hj; exact hj
      · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨hs, hs⟩
    · have hj := hc0
      dsimp only
      unfold lcre at hj ⊢
      rw [getD_snoc1] at hj
      by_cases h0 : 0 < l₁.length
      · rw [if_pos h0] at hj; exact hj
      · rw [List.getD_eq_default _ _ (by omega)]
    · have hj := hc0'
      dsimp only
      unfold lcre at hj ⊢
      rw [getD_snoc1] at hj
      by_cases h0 : 0 < l₁.length
      · rw [if_pos h0] at hj; exact hj
      · rw [List.getD_eq_default _ _ (by omega)]
  | weak bs bs' a a' hl hle hha =>
    subst hm
    simp only at ha
    set cr := bL.map Prod.snd with hcr
    have hlen : bs'.length = cr.length := by rw [hl, hcr, List.length_map, List.length_map]
    set nb := bs'.zip cr with hnb
    have hparts := getD_zip_parts bs' cr hlen
    have hnbl : nb.length = bL.length := by
      rw [hnb, List.length_zip, hlen, hcr, List.length_map, min_self]
    have hsupnb : ∀ j, lsup nb j = bs'.getD j 0 := fun j => (hparts j).1
    have hcrenb : ∀ j, lcre nb j = lcre bL j := by
      intro j
      unfold lcre
      rw [(hparts j).2, hcr]
      rw [show ((0 : ℝ), (0 : ℝ)) = Prod.snd ((0 : ℝ), (0 : ℝ), (0 : ℝ)) from rfl, List.getD_map]
    have hsupL : ∀ j, lsup bL j = (bL.map Prod.fst).getD j 0 := fun j => (getD_map_fst bL j).symm
    have hmono : ∀ j, lsup bL j ≤ lsup nb j := by
      intro j; rw [hsupnb, hsupL]; exact hle j
    refine ⟨(nb, a', lL), LStep.weak bL nb aL a' lL lL hnbl hmono hcrenb (by rw [ha]; exact hha)
      le_rfl, ?_⟩
    refine ⟨?_, rfl, hl0, ?_, ?_, ?_, ?_, ?_⟩
    · apply List.ext_getElem
      · rw [List.length_map, hnbl, hl, List.length_map]
      · intro j h1 h2
        rw [List.getElem_map]
        have := hsupnb j
        unfold lsup at this
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map] at h1; exact h1),
          List.getD_eq_getElem _ _ h2] at this
        exact this
    · have : ltop bL ≤ ltop nb := by
        unfold ltop; rw [hnbl]; exact hmono _
      linarith
    · intro j; exact le_trans (hsup j) (hmono j)
    · intro j; rw [hcrenb]; exact ⟨le_trans (hcre j).1 (hmono j), le_trans (hcre j).2 (hmono j)⟩
    · rw [hcrenb]; exact hc0
    · rw [hcrenb]; exact hc0'

open Classical in
noncomputable def liftSeq (c : ℝ) (L : ℕ → RLine) : ℕ → LLine
  | 0 => ([], (L 0).2, 0)
  | i + 1 =>
    if h : ∃ L', LStep c (liftSeq c L i) L' ∧ Emb (L (i + 1)) L' then Classical.choose h
    else ([], 0, 0)

theorem step1_refutation_lifts {c : ℝ} {n : ℕ} {L : ℕ → RLine}
    (h : RefutesWith (Step c 1) n L) : LRefutes c n (liftSeq c L) := by
  obtain ⟨hn, h0, hN, ha, hlt, hstep, hmid⟩ := h
  have hemb : ∀ i, i ≤ n → Emb (L i) (liftSeq c L i) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨by simp [liftSeq, h0], rfl, le_rfl, by simp [liftSeq, ltop, lsup], ?_, ?_, ?_, ?_⟩
      · intro j; simp [liftSeq, lsup]
      · intro j; simp [liftSeq, lcre, lsup]
      · simp [liftSeq, lcre]
      · simp [liftSeq, lcre]
    | succ i ih =>
      intro hi
      have hex := step_lift (hstep i (by omega)) (ih (by omega))
      have e : liftSeq c L (i + 1) = Classical.choose hex := by
        simp only [liftSeq, dif_pos hex]
      rw [e]; exact (Classical.choose_spec hex).2
  have hst : ∀ i, i < n → LStep c (liftSeq c L i) (liftSeq c L (i + 1)) := by
    intro i hi
    have hex := step_lift (hstep i hi) (hemb i hi.le)
    have e : liftSeq c L (i + 1) = Classical.choose hex := by
      simp only [liftSeq, dif_pos hex]
    rw [e]; exact (Classical.choose_spec hex).1
  have hlen : ∀ i, i ≤ n → (liftSeq c L i).1.map Prod.fst = (L i).1 := fun i hi => (hemb i hi).1
  have ha' : ∀ i, i ≤ n → (liftSeq c L i).2.1 = (L i).2 := fun i hi => (hemb i hi).2.1
  refine ⟨hn, by simp [liftSeq], ?_, by rw [ha' 0 (by omega)]; exact ha, le_rfl, ?_, hst, ?_⟩
  · have := hlen n le_rfl; rw [hN] at this; exact List.map_eq_nil_iff.mp this
  · rw [ha' n le_rfl, ha' 0 (by omega)]; exact hlt
  · intro i h1 h2 hnil
    have := hlen i h2.le
    rw [hnil] at this
    exact hmid i h1 h2 (by simpa using this.symm)

theorem bw_beta1_via_potential {c : ℝ} (hc : r7 ≤ c) (n : ℕ) (L : ℕ → RLine) :
    ¬ RefutesWith (Step c 1) n L := fun h => no_refutation_loc hc n _ (step1_refutation_lifts h)

end PastaMath.SatBarriers
