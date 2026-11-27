-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.LocalizedTrace

namespace PastaMath.SatBarriers

inductive LStepX (c β : ℝ) : LLine → LLine → Prop
  | init (a l : ℝ) : LStepX c β ([], a, l) ([(0, 0, 0)], a, l)
  | speed (bs : List LBlock) (b xc lc a l x b₁ b₂ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₁ : max x b ≤ b₁) (h₂ : l ≤ b₂) (h₃ : a - x ≤ a₂) :
      LStepX c β (bs ++ [(b, xc, lc)], a, l) (bs ++ [(b₁, xc, lc), (b₂, x, l)], a₂, l)
  | speedT (bs : List LBlock) (b xc lc a l x b₁ b₂ a₂ l₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₁ : max x b ≤ b₁) (h₂ : a - x ≤ b₂) (h₃ : a - x ≤ a₂) (h₄ : 0 ≤ l₂) :
      LStepX c β (bs ++ [(b, xc, lc)], a, l) (bs ++ [(b₁, xc, lc), (b₂, x, l)], a₂, l₂)
  | slow (bs : List LBlock) (b xc lc a l e l' : ℝ) (h₁ : c * max (max b a) lc ≤ e)
      (h₂ : ltop bs + β * (c - 1) * max (max b a) lc ≤ e ∨ ltop bs + β * (c - 1) * l' ≤ e)
      (h₃ : lc ≤ l') (h₄ : 0 ≤ l')
      (h₅ : xc + c * max (max b a) lc ≤ e + l') : LStepX c β (bs ++ [(b, xc, lc)], a, l) (bs, e, l')
  | weak (bs bs' : List LBlock) (a a' l l' : ℝ) (hl : bs'.length = bs.length)
      (hle : ∀ i, lsup bs i ≤ lsup bs' i) (hcr : ∀ i, lcre bs' i = lcre bs i) (ha : a ≤ a')
      (hll : l ≤ l') : LStepX c β (bs, a, l) (bs', a', l')

def LRefutesX (c β : ℝ) (n : ℕ) (L : ℕ → LLine) : Prop :=
  1 ≤ n ∧ (L 0).1 = [] ∧ (L n).1 = [] ∧ 0 ≤ (L 0).2.1 ∧ 0 ≤ (L 0).2.2 ∧
    (L n).2.1 < (L 0).2.1 ∧ (∀ i < n, LStepX c β (L i) (L (i + 1))) ∧
    (∀ i, 0 < i → i < n → (L i).1 ≠ [])

theorem lstepX_inv {c β : ℝ} {L L' : LLine} (h : LStepX c β L L') :
    (L.1 = [] ∧ L'.1 = [(0, 0, 0)] ∧ L'.2 = L.2) ∨
    (∃ (bs : List LBlock) (b xc lc x b₁ b₂ : ℝ), 0 ≤ x ∧ x ≤ L.2.1 ∧ max x b ≤ b₁ ∧
      ((L.2.2 ≤ b₂ ∧ L'.2.2 = L.2.2) ∨ (L.2.1 - x ≤ b₂ ∧ 0 ≤ L'.2.2)) ∧ L.2.1 - x ≤ L'.2.1 ∧
      L.1 = bs ++ [(b, xc, lc)] ∧ L'.1 = bs ++ [(b₁, xc, lc), (b₂, x, L.2.2)]) ∨
    (∃ b xc lc : ℝ, L.1 = L'.1 ++ [(b, xc, lc)] ∧ c * max (max b L.2.1) lc ≤ L'.2.1 ∧
      (ltop L'.1 + β * (c - 1) * max (max b L.2.1) lc ≤ L'.2.1 ∨
        ltop L'.1 + β * (c - 1) * L'.2.2 ≤ L'.2.1) ∧ lc ≤ L'.2.2 ∧ 0 ≤ L'.2.2 ∧
      xc + c * max (max b L.2.1) lc ≤ L'.2.1 + L'.2.2) ∨
    (L'.1.length = L.1.length ∧ (∀ i, lsup L.1 i ≤ lsup L'.1 i) ∧
      (∀ i, lcre L'.1 i = lcre L.1 i) ∧ L.2.1 ≤ L'.2.1 ∧ L.2.2 ≤ L'.2.2) := by
  cases h with
  | init a l => exact Or.inl ⟨rfl, rfl, rfl⟩
  | speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact Or.inr (Or.inl ⟨bs, b, xc, lc, x, b₁, b₂, hx, hxa, h₁, Or.inl ⟨h₂, rfl⟩, h₃, rfl, rfl⟩)
  | speedT bs b xc lc a l x b₁ b₂ a₂ l₂ hx hxa h₁ h₂ h₃ h₄ =>
    exact Or.inr (Or.inl ⟨bs, b, xc, lc, x, b₁, b₂, hx, hxa, h₁, Or.inr ⟨h₂, h₄⟩, h₃, rfl, rfl⟩)
  | slow bs b xc lc a l e l' h₁ h₂ h₃ h₄ h₅ =>
    exact Or.inr (Or.inr (Or.inl ⟨b, xc, lc, rfl, h₁, h₂, h₃, h₄, h₅⟩))
  | weak bs bs' a a' l l' hl hle hcr ha hll =>
    exact Or.inr (Or.inr (Or.inr ⟨hl, hle, hcr, ha, hll⟩))

theorem lstepX_len {c β : ℝ} {L L' : LLine} (h : LStepX c β L L') :
    L'.1.length ≤ L.1.length + 1 ∧ L.1.length ≤ L'.1.length + 1 := by
  rcases lstepX_inv h with ⟨h1, h2, _⟩ | ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, h1, h2⟩ |
    ⟨b, xc, lc, h1, -⟩ | ⟨h1, -⟩
  · rw [h1, h2]; simp
  · rw [h1, h2]; simp
  · rw [h1]; simp only [List.length_append, List.length_singleton]; omega
  · omega

theorem lstepX_nonneg {c β : ℝ} (hc : 0 ≤ c) {L L' : LLine} (h : LStepX c β L L') (ha : 0 ≤ L.2.1)
    (hl : 0 ≤ L.2.2) : 0 ≤ L'.2.1 ∧ 0 ≤ L'.2.2 := by
  rcases lstepX_inv h with ⟨-, -, h3⟩ | ⟨bs, b, xc, lc, x, b₁, b₂, -, hxa, -, hcase, h3, -, -⟩ |
    ⟨b, xc, lc, -, h3, -, -, h4, -⟩ | ⟨-, -, -, h3, h4⟩
  · rw [h3]; exact ⟨ha, hl⟩
  · refine ⟨by linarith, ?_⟩
    rcases hcase with ⟨-, h4⟩ | ⟨-, h4⟩
    · rw [h4]; exact hl
    · exact h4
  · exact ⟨le_trans (mul_nonneg hc (le_trans ha (le_trans (le_max_right _ _) (le_max_left _ _)))) h3, h4⟩
  · exact ⟨by linarith, by linarith⟩


theorem lstepX_mono {c β : ℝ} {L L' : LLine} (h : LStepX c β L L') {i : ℕ} (hi : i < L.1.length)
    (hi' : i < L'.1.length) : lsup L.1 i ≤ lsup L'.1 i ∧ lcre L'.1 i = lcre L.1 i := by
  rcases lstepX_inv h with ⟨h1, -, -⟩ | ⟨bs, b, xc, lc, x, b₁, b₂, -, -, hb, -, -, h1, h2⟩ |
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


theorem lsegmentX {c β : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hcub : (1 - β) * (c - 1) ^ 2 ≤ cub c) (L : ℕ → LLine) :
    ∀ len p k : ℕ, (∀ i, p ≤ i → i < p + len → LStepX c β (L i) (L (i + 1))) →
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
  rcases lstepX_inv hs0 with ⟨h1, -, -⟩ |
    ⟨bs, b, xc, lc, x, b₁, b₂, hx, hxa, h₁, hcase, h₃, e0, e1⟩ | ⟨b, xc, lc, e0, -⟩ |
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
      have h2 := (lstepX_len hsA).2
      omega
    rcases lstepX_inv hsA with ⟨h1, -, -⟩ |
      ⟨bs', b', xc', lc', x', b₁', b₂', -, -, -, -, -, f0, f1⟩ |
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
          have m1 := lstepX_mono hs (i := k) (by omega) (by omega)
          have m2 := lstepX_mono hs (i := k + 1) (by omega) (by omega)
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
      rw [hlc] at hu1 hu2 hu3 hu5
      rw [hxc] at hu5
      have hbtop : ltop (L p).1 = b := by rw [e0, ltop_app]
      rw [hbtop]
      have hl0 := (hdep p le_rfl (by omega)).2.2
      have hMA : PsiB c β (L p).2.2 ((L p).2.1 - x) (L p).2.2 ≤
          max (max y (L (m0 - 1)).2.1) (L p).2.2 :=
        start_bound hc1 hβ0 hl0 (by linarith) hcase h₃ hA
      have hXx : x ≤ ltop (L m0).1 := le_trans (le_max_left _ _) (le_trans h₁ hXX)
      have hXb : b ≤ ltop (L m0).1 := le_trans (le_max_right _ _) (le_trans h₁ hXX)
      have hk : 0 ≤ β * (c - 1) := mul_nonneg hβ0 (by linarith)
      have hMl : (L p).2.2 ≤ max (max y (L (m0 - 1)).2.1) (L p).2.2 := le_max_right _ _
      have hM0 : 0 ≤ max (max y (L (m0 - 1)).2.1) (L p).2.2 := le_trans hl0 hMl
      have hu2x : x + β * (c - 1) * max (max y (L (m0 - 1)).2.1) (L p).2.2 ≤ (L m0).2.1 := by
        rcases hu2 with h | h
        · linarith
        · have g1 := mul_le_mul_of_nonneg_left hu5 hk
          have g2 : β * (c - 1) * ((1 + β * (c - 1)) * max (max y (L (m0 - 1)).2.1) (L p).2.2) ≤
              β * (c - 1) * (c * max (max y (L (m0 - 1)).2.1) (L p).2.2) := by
            apply mul_le_mul_of_nonneg_left _ hk
            apply mul_le_mul_of_nonneg_right _ hM0
            have : β * (c - 1) ≤ 1 * (c - 1) := mul_le_mul_of_nonneg_right hβ1 (by linarith)
            linarith
          have hpos : 0 < 1 + β * (c - 1) := by linarith
          have key : (1 + β * (c - 1)) *
              (x + β * (c - 1) * max (max y (L (m0 - 1)).2.1) (L p).2.2 - (L m0).2.1) ≤
              (1 + β * (c - 1)) * 0 := by
            have := mul_le_mul_of_nonneg_left hu3 hk
            nlinarith
          have := le_of_mul_le_mul_left key hpos
          linarith
      have hu2b : b + β * (c - 1) * (L p).2.2 ≤ (L m0).2.1 := by
        rcases hu2 with h | h
        · have := mul_le_mul_of_nonneg_left hMl hk; linarith
        · have := mul_le_mul_of_nonneg_left hu3 hk; linarith
      have hstepP := psiB_step_gen (X := ltop (L m0).1) hc hc2 hβ0 hβ1 hcub hl0 hx hxa hXx hXb
        hMA hu1 hu2x hu2b hu3 hu5
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

theorem lnoX_refutation_core {c β : ℝ} (hc : 9 / 5 ≤ c) (hc2 : c ≤ 2) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hcub : (1 - β) * (c - 1) ^ 2 ≤ cub c) (n : ℕ)
    (L : ℕ → LLine) : ¬ LRefutesX c β n L := by
  rintro ⟨hn, h0, hN, ha, hl, hlt, hstep, hmid⟩
  have hc0 : (0 : ℝ) < c := by linarith
  have hnn : ∀ i, i ≤ n → 0 ≤ (L i).2.1 ∧ 0 ≤ (L i).2.2 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨ha, hl⟩
    | succ i ih =>
      intro hi
      obtain ⟨a1, a2⟩ := ih (by omega)
      exact lstepX_nonneg hc0.le (hstep i (by omega)) a1 a2
  rcases lstepX_inv (hstep 0 (by omega)) with ⟨-, h1, h2⟩ |
    ⟨bs, b, xc, lc, x, b₁, b₂, -, -, -, -, -, e0, -⟩ | ⟨b, xc, lc, e0, -⟩ | ⟨hl0, -, -, ha', -⟩
  · rcases Nat.lt_or_ge 1 n with hn1 | hn1
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
        have hseg := lsegmentX hc hc2 hβ0 hβ1 hcub L (n - 2) 1 0
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

theorem lstepX_restrict {c c₀ β : ℝ} (hβ : 0 ≤ β) (hcc : c₀ ≤ c) {L L' : LLine}
    (h : LStepX c β L L') (ha : 0 ≤ L.2.1) : LStepX c₀ β L L' := by
  cases h with
  | init a l => exact LStepX.init a l
  | speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact LStepX.speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃
  | speedT bs b xc lc a l x b₁ b₂ a₂ l₂ hx hxa h₁ h₂ h₃ h₄ =>
    exact LStepX.speedT bs b xc lc a l x b₁ b₂ a₂ l₂ hx hxa h₁ h₂ h₃ h₄
  | weak bs bs' a a' l l' hl hle hcr hha hll => exact LStepX.weak bs bs' a a' l l' hl hle hcr hha hll
  | slow bs b xc lc a l e l' h₁ h₂ h₃ h₄ h₅ =>
    have hM : 0 ≤ max (max b a) lc := le_trans ha (le_trans (le_max_right _ _) (le_max_left _ _))
    have k := mul_le_mul_of_nonneg_right hcc hM
    have k2 := mul_le_mul_of_nonneg_left k hβ
    have k3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcc h₄) hβ
    refine LStepX.slow bs b xc lc a l e l' (by linarith) ?_ h₃ h₄ (by linarith)
    rcases h₂ with h | h
    · left; nlinarith
    · right; nlinarith

theorem no_refutation_locX {c β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hc1 : 1 ≤ c)
    (hcub : (1 - β) * (c - 1) ^ 2 ≤ cub c) (n : ℕ) (L : ℕ → LLine) : ¬ LRefutesX c β n L := by
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
      exact lstepX_nonneg hc0 (hstep i (by omega)) a1 a2
  rcases le_total c 2 with hc2 | hc2
  · exact lnoX_refutation_core h95 hc2 hβ0 hβ1 hcub n L ⟨hn, h0, hN, ha, hl, hlt, hstep, hmid⟩
  · apply lnoX_refutation_core (c := 2) (by norm_num) le_rfl hβ0 hβ1 (by unfold cub; nlinarith) n L
    exact ⟨hn, h0, hN, ha, hl, hlt,
      fun i hi => lstepX_restrict hβ0 hc2 (hstep i hi) (hnn i hi.le).1, hmid⟩



theorem lstepT_lstepX {c β : ℝ} {L L' : LLine} (h : LStepT c β L L') : LStepX c β L L' := by
  cases h with
  | init a l => exact LStepX.init a l
  | speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact LStepX.speed bs b xc lc a l x b₁ b₂ a₂ hx hxa h₁ h₂ h₃
  | speedT bs b xc lc a l x b₁ b₂ a₂ l₂ hx hxa h₁ h₂ h₃ h₄ =>
    exact LStepX.speedT bs b xc lc a l x b₁ b₂ a₂ l₂ hx hxa h₁ h₂ h₃ h₄
  | slow bs b xc lc a l e l' h₁ h₂ h₃ h₄ h₅ => exact LStepX.slow bs b xc lc a l e l' h₁ (Or.inl h₂) h₃ h₄ h₅
  | weak bs bs' a a' l l' hl hle hcr hha hll => exact LStepX.weak bs bs' a a' l l' hl hle hcr hha hll

theorem lstepX_local_only_witness {c : ℝ} (h10 : c ≤ 10) :
    LStepX c 1 ([(10, 0, 0), (1, 0, 0)], 1, 0) ([(10, 0, 0)], 10, 0) ∧
      (1 < c → 10 < ltop [((10 : ℝ), (0 : ℝ), (0 : ℝ))] + 1 * (c - 1) * max (max 1 1) 0) := by
  refine ⟨?_, fun h1 => by simp [ltop, lsup]; linarith⟩
  have h := LStepX.slow (c := c) (β := 1) [(10, 0, 0)] 1 0 0 1 0 10 0 (by simp; linarith)
    (Or.inr (by simp [ltop, lsup])) le_rfl le_rfl (by simp; linarith)
  exact h

end PastaMath.SatBarriers
