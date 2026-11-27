-- SPDX-License-Identifier: Apache-2.0
import PastaMath.FastDiag.Moment

namespace PastaMath.FastDiag

open Finset

theorem blocks_le_of_ratio {t a b n : ℕ} (ht : (t - 1) * b < n) (hab : 16 * a ≤ b)
    (han : 16 * a ≤ n) : 8 * t * a ≤ n := by
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0; simp
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ht
    have h1 : 16 * a * u ≤ b * u := Nat.mul_le_mul_right u hab
    nlinarith

theorem potential_params_lt {t : ℕ} (b : Fin t → ℕ) (k D a n cardΔ : ℕ)
    (hn : ∑ ℓ, b ℓ = n) (hΔ : cardΔ ≤ 2 ^ D) (hk : k ≤ 2 ^ a) (hta : 8 * t * a ≤ n)
    (hD : 2 * D ≤ k * n) (hpos : 0 < k * n) :
    cardΔ * ∏ ℓ, (k ^ (2 * k) * (2 ^ b ℓ) ^ k) < (∏ ℓ, 2 ^ b ℓ) ^ (2 * k) := by
  have hfac : ∀ ℓ, k ^ (2 * k) * (2 ^ b ℓ) ^ k ≤ 2 ^ (2 * a * k + b ℓ * k) := by
    intro ℓ
    rw [pow_add, ← pow_mul]
    have : k ^ (2 * k) ≤ 2 ^ (2 * a * k) := by
      calc k ^ (2 * k) ≤ (2 ^ a) ^ (2 * k) := Nat.pow_le_pow_left hk _
        _ = 2 ^ (2 * a * k) := by rw [← pow_mul]; ring_nf
    exact Nat.mul_le_mul_right _ this
  have hprod : ∏ ℓ, (k ^ (2 * k) * (2 ^ b ℓ) ^ k) ≤ 2 ^ (2 * a * k * t + n * k) := by
    calc ∏ ℓ, (k ^ (2 * k) * (2 ^ b ℓ) ^ k) ≤ ∏ ℓ : Fin t, 2 ^ (2 * a * k + b ℓ * k) :=
          Finset.prod_le_prod' (fun ℓ _ => hfac ℓ)
      _ = 2 ^ (∑ ℓ : Fin t, (2 * a * k + b ℓ * k)) := Finset.prod_pow_eq_pow_sum _ _ _
      _ = 2 ^ (2 * a * k * t + n * k) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, hn]
          simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
          ring
  have hrhs : (∏ ℓ : Fin t, 2 ^ b ℓ) ^ (2 * k) = 2 ^ (2 * n * k) := by
    rw [Finset.prod_pow_eq_pow_sum, hn, ← pow_mul]; ring_nf
  rw [hrhs]
  calc cardΔ * ∏ ℓ, (k ^ (2 * k) * (2 ^ b ℓ) ^ k)
      ≤ 2 ^ D * 2 ^ (2 * a * k * t + n * k) := Nat.mul_le_mul hΔ hprod
    _ = 2 ^ (D + (2 * a * k * t + n * k)) := by rw [← pow_add]
    _ < 2 ^ (2 * n * k) := by
        apply Nat.pow_lt_pow_right (by norm_num)
        have h1 : 8 * t * a * k ≤ n * k := Nat.mul_le_mul_right k hta
        nlinarith

theorem exists_hard_blockXor_of_params {t : ℕ} {Y : Fin t → Type*} [∀ ℓ, Fintype (Y ℓ)]
    [∀ ℓ, DecidableEq (Y ℓ)] {Δ : Type*} [Fintype Δ] (C : Δ → (∀ ℓ, Y ℓ) → Bool)
    (b : Fin t → ℕ) (k D a n : ℕ) (hY : ∀ ℓ, Fintype.card (Y ℓ) = 2 ^ b ℓ)
    (hn : ∑ ℓ, b ℓ = n) (hΔ : Fintype.card Δ ≤ 2 ^ D) (hk : k ≤ 2 ^ a)
    (hta : 8 * t * a ≤ n) (hD : 2 * D ≤ k * n) (hpos : 0 < k * n) :
    ∃ T : (∀ ℓ, Y ℓ → Bool), ∀ d, C d ≠ blockXor T := by
  apply exists_hard_blockXor C k
  simp_rw [hY]
  exact potential_params_lt b k D a n _ hn hΔ hk hta hD hpos

theorem expected_potential_lt_of_params {t : ℕ} {Y : Fin t → Type*} [∀ ℓ, Fintype (Y ℓ)]
    [∀ ℓ, DecidableEq (Y ℓ)] {Δ : Type*} [Fintype Δ] (C : Δ → (∀ ℓ, Y ℓ) → Bool)
    (b : Fin t → ℕ) (k D a n : ℕ) (hY : ∀ ℓ, Fintype.card (Y ℓ) = 2 ^ b ℓ)
    (hn : ∑ ℓ, b ℓ = n) (hΔ : Fintype.card Δ ≤ 2 ^ D) (hk : k ≤ 2 ^ a)
    (hta : 8 * t * a ≤ n) (hD : 2 * D ≤ k * n) (hpos : 0 < k * n) :
    ∑ T : (∀ ℓ, Y ℓ → Bool), ∑ d, corr (C d) (blockXor T) ^ (2 * k)
      < (Fintype.card (∀ ℓ, Y ℓ → Bool) : ℤ) * (Fintype.card (∀ ℓ, Y ℓ) : ℤ) ^ (2 * k) := by
  have hup := potential_sum_le C (fun T => blockXor T) (2 * k) (blockGood (2 * k))
    (fun x => blockXor_sign_sum (2 * k) x)
  have hgood := blockGood_card_le (Y := Y) k
  have hlt := potential_params_lt b k D a n (Fintype.card Δ) hn hΔ hk hta hD hpos
  have hlt' : Fintype.card Δ * (blockGood (Y := Y) (2 * k)).card
      < Fintype.card (∀ ℓ, Y ℓ) ^ (2 * k) := by
    rw [Fintype.card_pi]
    calc Fintype.card Δ * (blockGood (Y := Y) (2 * k)).card
        ≤ Fintype.card Δ * ∏ ℓ, (k ^ (2 * k) * Fintype.card (Y ℓ) ^ k) :=
          Nat.mul_le_mul_left _ hgood
      _ < (∏ ℓ, Fintype.card (Y ℓ)) ^ (2 * k) := by simp_rw [hY]; exact hlt
  have hlt'' : (Fintype.card Δ : ℤ) * (blockGood (Y := Y) (2 * k)).card
      < (Fintype.card (∀ ℓ, Y ℓ) : ℤ) ^ (2 * k) := by exact_mod_cast hlt'
  have hΩ : (0 : ℤ) < Fintype.card (∀ ℓ, Y ℓ → Bool) := by exact_mod_cast Fintype.card_pos
  calc ∑ T : (∀ ℓ, Y ℓ → Bool), ∑ d, corr (C d) (blockXor T) ^ (2 * k)
      ≤ (Fintype.card Δ : ℤ) * (blockGood (Y := Y) (2 * k)).card *
          Fintype.card (∀ ℓ, Y ℓ → Bool) := hup
    _ < (Fintype.card (∀ ℓ, Y ℓ → Bool) : ℤ) * (Fintype.card (∀ ℓ, Y ℓ) : ℤ) ^ (2 * k) := by
        rw [mul_comm ((Fintype.card (∀ ℓ, Y ℓ → Bool) : ℤ))]
        exact mul_lt_mul_of_pos_right hlt'' hΩ

end PastaMath.FastDiag
