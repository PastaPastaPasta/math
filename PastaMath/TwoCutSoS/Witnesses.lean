-- SPDX-License-Identifier: Apache-2.0
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PastaMath.TwoCutSoS.Defs

/-!
# Explicit constructions and border decompositions for two-cut rank

Proves over arbitrary fields `K` (characteristic ≠ 2 for the Clifford construction;
**every** field `K`, including characteristic `2`, for the integer schemes and border theorem):
* `clifford_twoCut`: `n` anticommuting square roots of the identity in `M_d(K)` yield a self-dual
  two-cut decomposition `TC_K(d, n) ≤ 2d` (`char K ≠ 2`).
* `exact_of_border_coeffs`: a pole-order-`k` border two-cut decomposition of ranks `(a, b)`
  yields an exact two-cut decomposition of cost `≤ (k + 1) * (a + b)` (`TC ≤ (k + 1) bTC_k`).
* `tc45_twoCut`, `tc46_twoCut`, `tc88_twoCut`: exact ±1 integer schemes giving
  `TC_K(4, 5) ≤ 8`, `TC_K(4, 6) ≤ 8`, and `TC_K(8, 8) ≤ 16` over every field `K`.
* `border44_identity_field`: exact ±1 pole-order-2 border decomposition `bTC_K(4, 4) ≤ 6`
  (ranks `3 + 3`) over every field `K`, checked by `decide`.
-/

namespace PastaMath.TwoCutSoS

open Matrix Finset

section CliffordAndBorder

variable {K : Type*} [Field K]

/-- Clifford self-dual decomposition: if `γ_i γ_j + γ_j γ_i = 2 δ_{ij} I_d` (`char K ≠ 2`),
then `M((a, i), (c, j)) = (γ_i γ_j)_{a, c} / 2` satisfies `M + M^Γ = 1`. -/
theorem clifford_selfdual {d n : ℕ} (γ : Fin n → Matrix (Fin d) (Fin d) K)
    (hγ : ∀ i j, γ i * γ j + γ j * γ i =
      if i = j then (2 : K) • (1 : Matrix (Fin d) (Fin d) K) else 0)
    (h2 : (2 : K) ≠ 0) :
    (Matrix.of fun (p q : Fin d × Fin n) => (γ p.2 * γ q.2) p.1 q.1 / 2) +
      ptr (Matrix.of fun (p q : Fin d × Fin n) => (γ p.2 * γ q.2) p.1 q.1 / 2) = 1 := by
  ext ⟨a, i⟩ ⟨c, j⟩
  simp only [Matrix.add_apply, ptr_apply, Matrix.of_apply]
  have h := congrArg (fun X : Matrix (Fin d) (Fin d) K => X a c) (hγ i j)
  simp only [Matrix.add_apply] at h
  rw [← add_div, h]
  by_cases hij : i = j
  · subst hij
    by_cases hac : a = c
    · subst hac; simp [h2]
    · simp [hac, Prod.ext_iff]
  · simp [hij, Prod.ext_iff]

/-- The Clifford matrix has rank at most `d`. -/
theorem clifford_rank_le {d n : ℕ} (γ : Fin n → Matrix (Fin d) (Fin d) K) :
    (Matrix.of fun (p q : Fin d × Fin n) => (γ p.2 * γ q.2) p.1 q.1 / 2).rank ≤ d := by
  have hfac : (Matrix.of fun (p q : Fin d × Fin n) => (γ p.2 * γ q.2) p.1 q.1 / 2) =
      (Matrix.of fun (p : Fin d × Fin n) (k : Fin d) => γ p.2 p.1 k / 2) *
        (Matrix.of fun (k : Fin d) (q : Fin d × Fin n) => γ q.2 k q.1) := by
    ext p q
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by rw [div_eq_mul_inv]; ring
  rw [hfac]
  calc _ ≤ (Matrix.of fun (p : Fin d × Fin n) (k : Fin d) => γ p.2 p.1 k / 2).rank :=
        Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin d) := Matrix.rank_le_card_width _
    _ = d := Fintype.card_fin d

/-- Clifford upper bound: `n` anticommuting square roots of `1` in `M_d(K)` give
`TC_K(d, n) ≤ 2d` (`char K ≠ 2`). -/
theorem clifford_twoCut {d n : ℕ} (γ : Fin n → Matrix (Fin d) (Fin d) K)
    (hγ : ∀ i j, γ i * γ j + γ j * γ i =
      if i = j then (2 : K) • (1 : Matrix (Fin d) (Fin d) K) else 0)
    (h2 : (2 : K) ≠ 0) :
    HasTwoCut (1 : Matrix (Fin d × Fin n) (Fin d × Fin n) K) (2 * d) := by
  refine ⟨_, _, clifford_selfdual γ hγ h2, ?_⟩
  have := clifford_rank_le (K := K) γ
  omega

/-- A sum of `|S|` matrices of rank `≤ c` has rank `≤ |S| * c`. -/
theorem rank_sum_le_card_mul {ι m n : Type*} [Fintype m] [Fintype n] [DecidableEq ι]
    (S : Finset ι) (M : ι → Matrix m n K) (c : ℕ) (h : ∀ i ∈ S, (M i).rank ≤ c) :
    (∑ i ∈ S, M i).rank ≤ S.card * c := by
  calc (∑ i ∈ S, M i).rank ≤ ∑ i ∈ S, (M i).rank := rank_sum_le' S M
    _ ≤ ∑ _i ∈ S, c := Finset.sum_le_sum h
    _ = S.card * c := by rw [Finset.sum_const, smul_eq_mul]

/-- The `ε⁰` coefficient of a pole-order-`k` rank-`a` family `U(ε) V(ε)ᵀ / εᵏ`
has rank at most `(k + 1) * a`. -/
theorem pole_coeff_rank_le {n : Type*} [Fintype n] {a : ℕ} (k : ℕ)
    (U V : ℕ → Matrix n (Fin a) K) :
    (∑ i ∈ Finset.range (k + 1), U i * (V (k - i))ᵀ).rank ≤ (k + 1) * a := by
  have h := rank_sum_le_card_mul (Finset.range (k + 1)) (fun i => U i * (V (k - i))ᵀ) a
    (fun i _ => by
      calc (U i * (V (k - i))ᵀ).rank ≤ (U i).rank := Matrix.rank_mul_le_left _ _
        _ ≤ Fintype.card (Fin a) := Matrix.rank_le_card_width _
        _ = a := Fintype.card_fin a)
  simpa [Finset.card_range] using h

/-- Border-to-exact conversion: a pole-order-`k` border two-cut decomposition of ranks `a` and `b`
yields an exact two-cut decomposition of cost at most `(k + 1) * (a + b)` over every field `K`. -/
theorem exact_of_border_coeffs {r s a b : ℕ} (k : ℕ)
    (U V : ℕ → Matrix (Fin r × Fin s) (Fin a) K) (X Y : ℕ → Matrix (Fin r × Fin s) (Fin b) K)
    (h : (∑ i ∈ Finset.range (k + 1), U i * (V (k - i))ᵀ) +
      ptr (∑ i ∈ Finset.range (k + 1), X i * (Y (k - i))ᵀ) = 1) :
    HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) ((k + 1) * (a + b)) :=
  ⟨_, _, h, by rw [mul_add]; exact add_le_add (pole_coeff_rank_le k U V) (pole_coeff_rank_le k X Y)⟩

end CliffordAndBorder

section IntegerSchemes

/-- Integer outer product `u vᵀ` on `Fin r × Fin s`. -/
def vmvZ {r s : ℕ} (u v : Fin r × Fin s → ℤ) : Matrix (Fin r × Fin s) (Fin r × Fin s) ℤ :=
  Matrix.of fun p q => u p * v q

/-- Integer partial transpose on `Fin r × Fin s`. -/
def ptrZ {r s : ℕ} (M : Matrix (Fin r × Fin s) (Fin r × Fin s) ℤ) :
    Matrix (Fin r × Fin s) (Fin r × Fin s) ℤ :=
  Matrix.of fun p q => M (p.1, q.2) (q.1, p.2)

private lemma two_cut_cast {r s : ℕ} (PZ QZ : Matrix (Fin r × Fin s) (Fin r × Fin s) ℤ)
    (h : ∀ p q, (PZ + ptrZ QZ) p q = if p = q then 1 else 0) (K : Type*) [Field K] :
    (Int.castRingHom K).mapMatrix PZ + ptr ((Int.castRingHom K).mapMatrix QZ) = 1 := by
  ext p q
  have h1 := h p q
  simp only [Matrix.add_apply, RingHom.mapMatrix_apply, Matrix.map_apply, ptr_apply,
    Matrix.one_apply]
  change (PZ p q : K) + (ptrZ QZ p q : K) = if p = q then 1 else 0
  rw [← Int.cast_add]
  have h2 : PZ p q + ptrZ QZ p q = (PZ + ptrZ QZ) p q := rfl
  rw [h2, h1]
  split_ifs <;> simp

private lemma vmvZ_rank_le {r s : ℕ} (u v : Fin r × Fin s → ℤ) (K : Type*) [Field K] :
    ((Int.castRingHom K).mapMatrix (vmvZ u v)).rank ≤ 1 := by
  have hfac : (Int.castRingHom K).mapMatrix (vmvZ u v) =
      (Matrix.of fun p (_ : Fin 1) => (u p : K)) *
        (Matrix.of fun (_ : Fin 1) q => (v q : K)) := by
    ext p q; simp [vmvZ, Matrix.mul_apply]
  rw [hfac]
  calc _ ≤ (Matrix.of fun p (_ : Fin 1) => (u p : K)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_width _
    _ = 1 := Fintype.card_fin 1

private lemma rank_add_le_of {n : Type*} [Fintype n] {K : Type*} [Field K]
    {A B : Matrix n n K} {a b : ℕ} (ha : A.rank ≤ a) (hb : B.rank ≤ b) :
    (A + B).rank ≤ a + b :=
  (rank_add_le' A B).trans (Nat.add_le_add ha hb)

/-! ### Exact ±1 scheme for `TC_K(4, 5) ≤ 8` over every field `K` -/

private def tc45u0 : Fin 4 × Fin 5 → ℤ := fun p => if p = (0, 0) then 1 else if p = (1, 2) then 1 else if p = (3, 3) then 1 else 0
private def tc45u1 : Fin 4 × Fin 5 → ℤ := fun p => if p = (0, 1) then 1 else if p = (2, 2) then 1 else if p = (3, 4) then 1 else 0
private def tc45u2 : Fin 4 × Fin 5 → ℤ := fun p => if p = (1, 1) then 1 else if p = (2, 0) then -1 else 0
private def tc45u3 : Fin 4 × Fin 5 → ℤ := fun p => if p = (1, 4) then 1 else if p = (2, 3) then -1 else 0
private def tc45u4 : Fin 4 × Fin 5 → ℤ := fun p => if p = (0, 2) then 1 else if p = (1, 0) then -1 else if p = (2, 1) then -1 else 0
private def tc45u5 : Fin 4 × Fin 5 → ℤ := fun p => if p = (0, 3) then 1 else if p = (3, 0) then -1 else 0
private def tc45u6 : Fin 4 × Fin 5 → ℤ := fun p => if p = (0, 4) then 1 else if p = (3, 1) then -1 else 0
private def tc45u7 : Fin 4 × Fin 5 → ℤ := fun p => if p = (1, 3) then 1 else if p = (2, 4) then 1 else if p = (3, 2) then -1 else 0

private def tc45A : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℤ :=
  vmvZ tc45u0 tc45u0 + vmvZ tc45u1 tc45u1 + vmvZ tc45u2 tc45u2 + vmvZ tc45u3 tc45u3

private def tc45B : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℤ :=
  vmvZ tc45u4 tc45u4 + vmvZ tc45u5 tc45u5 + vmvZ tc45u6 tc45u6 + vmvZ tc45u7 tc45u7

private theorem tc45_coeff : ∀ p q : Fin 4 × Fin 5,
    (tc45A + ptrZ tc45B) p q = if p = q then 1 else 0 := by decide

/-- Exact ±1 scheme: `TC_K(4, 5) ≤ 8` over every field `K` (including `ℚ`, `ℝ`, and `char 2`). -/
theorem tc45_twoCut (K : Type*) [Field K] :
    HasTwoCut (1 : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) K) 8 := by
  refine ⟨(Int.castRingHom K).mapMatrix tc45A, (Int.castRingHom K).mapMatrix tc45B,
    two_cut_cast _ _ tc45_coeff K, ?_⟩
  have hA : ((Int.castRingHom K).mapMatrix tc45A).rank ≤ 4 := by
    simp only [tc45A, map_add]
    exact rank_add_le_of (rank_add_le_of (rank_add_le_of
      (vmvZ_rank_le _ _ K) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)
  have hB : ((Int.castRingHom K).mapMatrix tc45B).rank ≤ 4 := by
    simp only [tc45B, map_add]
    exact rank_add_le_of (rank_add_le_of (rank_add_le_of
      (vmvZ_rank_le _ _ K) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)
  omega

/-! ### Exact ±1 scheme for `TC_K(4, 6) ≤ 8` over every field `K` -/

private def tc46u0 : Fin 4 × Fin 6 → ℤ := fun p => if p = (0, 1) then 1 else if p = (2, 2) then 1 else if p = (3, 0) then 1 else 0
private def tc46u1 : Fin 4 × Fin 6 → ℤ := fun p => if p = (0, 4) then 1 else if p = (1, 2) then 1 else if p = (3, 3) then 1 else 0
private def tc46u2 : Fin 4 × Fin 6 → ℤ := fun p => if p = (0, 5) then 1 else if p = (1, 0) then 1 else if p = (2, 3) then -1 else 0
private def tc46u3 : Fin 4 × Fin 6 → ℤ := fun p => if p = (1, 1) then 1 else if p = (2, 4) then -1 else if p = (3, 5) then -1 else 0
private def tc46u4 : Fin 4 × Fin 6 → ℤ := fun p => if p = (0, 0) then 1 else if p = (1, 5) then -1 else if p = (3, 1) then -1 else 0
private def tc46u5 : Fin 4 × Fin 6 → ℤ := fun p => if p = (0, 2) then 1 else if p = (1, 4) then -1 else if p = (2, 1) then -1 else 0
private def tc46u6 : Fin 4 × Fin 6 → ℤ := fun p => if p = (0, 3) then 1 else if p = (2, 5) then 1 else if p = (3, 4) then -1 else 0
private def tc46u7 : Fin 4 × Fin 6 → ℤ := fun p => if p = (1, 3) then 1 else if p = (2, 0) then 1 else if p = (3, 2) then -1 else 0

private def tc46A : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℤ :=
  vmvZ tc46u0 tc46u0 + vmvZ tc46u1 tc46u1 + vmvZ tc46u2 tc46u2 + vmvZ tc46u3 tc46u3

private def tc46B : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℤ :=
  vmvZ tc46u4 tc46u4 + vmvZ tc46u5 tc46u5 + vmvZ tc46u6 tc46u6 + vmvZ tc46u7 tc46u7

private theorem tc46_coeff : ∀ p q : Fin 4 × Fin 6,
    (tc46A + ptrZ tc46B) p q = if p = q then 1 else 0 := by decide

/-- Exact ±1 scheme: `TC_K(4, 6) ≤ 8` over every field `K`. -/
theorem tc46_twoCut (K : Type*) [Field K] :
    HasTwoCut (1 : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) K) 8 := by
  refine ⟨(Int.castRingHom K).mapMatrix tc46A, (Int.castRingHom K).mapMatrix tc46B,
    two_cut_cast _ _ tc46_coeff K, ?_⟩
  have hA : ((Int.castRingHom K).mapMatrix tc46A).rank ≤ 4 := by
    simp only [tc46A, map_add]
    exact rank_add_le_of (rank_add_le_of (rank_add_le_of
      (vmvZ_rank_le _ _ K) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)
  have hB : ((Int.castRingHom K).mapMatrix tc46B).rank ≤ 4 := by
    simp only [tc46B, map_add]
    exact rank_add_le_of (rank_add_le_of (rank_add_le_of
      (vmvZ_rank_le _ _ K) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)
  omega

/-! ### Exact ±1 XOR-coset scheme for `TC_K(8, 8) ≤ 16` over every field `K` -/

private def tc88u0 : Fin 8 × Fin 8 → ℤ := fun p => if p = (0, 1) then 1 else if p = (2, 3) then 1 else if p = (4, 5) then 1 else if p = (6, 7) then 1 else 0
private def tc88u1 : Fin 8 × Fin 8 → ℤ := fun p => if p = (1, 0) then 1 else if p = (3, 2) then 1 else if p = (5, 4) then 1 else if p = (7, 6) then 1 else 0
private def tc88u2 : Fin 8 × Fin 8 → ℤ := fun p => if p = (0, 2) then 1 else if p = (2, 0) then 1 else if p = (5, 7) then 1 else if p = (7, 5) then 1 else 0
private def tc88u3 : Fin 8 × Fin 8 → ℤ := fun p => if p = (1, 3) then 1 else if p = (3, 1) then 1 else if p = (4, 6) then 1 else if p = (6, 4) then 1 else 0
private def tc88u4 : Fin 8 × Fin 8 → ℤ := fun p => if p = (0, 4) then 1 else if p = (3, 7) then -1 else if p = (4, 0) then 1 else if p = (7, 3) then -1 else 0
private def tc88u5 : Fin 8 × Fin 8 → ℤ := fun p => if p = (1, 5) then 1 else if p = (2, 6) then -1 else if p = (5, 1) then 1 else if p = (6, 2) then -1 else 0
private def tc88u6 : Fin 8 × Fin 8 → ℤ := fun p => if p = (0, 6) then 1 else if p = (3, 5) then -1 else if p = (5, 3) then 1 else if p = (6, 0) then -1 else 0
private def tc88u7 : Fin 8 × Fin 8 → ℤ := fun p => if p = (1, 7) then 1 else if p = (2, 4) then -1 else if p = (4, 2) then 1 else if p = (7, 1) then -1 else 0
private def tc88u8 : Fin 8 × Fin 8 → ℤ := fun p => if p = (0, 0) then 1 else if p = (2, 2) then -1 else if p = (4, 4) then -1 else if p = (6, 6) then 1 else 0
private def tc88u9 : Fin 8 × Fin 8 → ℤ := fun p => if p = (1, 1) then 1 else if p = (3, 3) then -1 else if p = (5, 5) then -1 else if p = (7, 7) then 1 else 0
private def tc88u10 : Fin 8 × Fin 8 → ℤ := fun p => if p = (0, 3) then 1 else if p = (2, 1) then -1 else if p = (5, 6) then -1 else if p = (7, 4) then 1 else 0
private def tc88u11 : Fin 8 × Fin 8 → ℤ := fun p => if p = (1, 2) then 1 else if p = (3, 0) then -1 else if p = (4, 7) then -1 else if p = (6, 5) then 1 else 0
private def tc88u12 : Fin 8 × Fin 8 → ℤ := fun p => if p = (0, 5) then 1 else if p = (3, 6) then 1 else if p = (4, 1) then -1 else if p = (7, 2) then -1 else 0
private def tc88u13 : Fin 8 × Fin 8 → ℤ := fun p => if p = (1, 4) then 1 else if p = (2, 7) then 1 else if p = (5, 0) then -1 else if p = (6, 3) then -1 else 0
private def tc88u14 : Fin 8 × Fin 8 → ℤ := fun p => if p = (0, 7) then 1 else if p = (3, 4) then 1 else if p = (5, 2) then -1 else if p = (6, 1) then -1 else 0
private def tc88u15 : Fin 8 × Fin 8 → ℤ := fun p => if p = (1, 6) then 1 else if p = (2, 5) then 1 else if p = (4, 3) then -1 else if p = (7, 0) then -1 else 0

private def tc88A : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℤ :=
  vmvZ tc88u0 tc88u0 + vmvZ tc88u1 tc88u1 + vmvZ tc88u2 tc88u2 + vmvZ tc88u3 tc88u3 +
  vmvZ tc88u4 tc88u4 + vmvZ tc88u5 tc88u5 + vmvZ tc88u6 tc88u6 + vmvZ tc88u7 tc88u7

private def tc88B : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℤ :=
  vmvZ tc88u8 tc88u8 + vmvZ tc88u9 tc88u9 + vmvZ tc88u10 tc88u10 + vmvZ tc88u11 tc88u11 +
  vmvZ tc88u12 tc88u12 + vmvZ tc88u13 tc88u13 + vmvZ tc88u14 tc88u14 + vmvZ tc88u15 tc88u15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tc88_coeff : ∀ p q : Fin 8 × Fin 8,
    (tc88A + ptrZ tc88B) p q = if p = q then 1 else 0 := by decide +kernel

/-- Exact ±1 XOR-coset scheme: `TC_K(8, 8) ≤ 16` over every field `K`. -/
theorem tc88_twoCut (K : Type*) [Field K] :
    HasTwoCut (1 : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) K) 16 := by
  refine ⟨(Int.castRingHom K).mapMatrix tc88A, (Int.castRingHom K).mapMatrix tc88B,
    two_cut_cast _ _ tc88_coeff K, ?_⟩
  have hA : ((Int.castRingHom K).mapMatrix tc88A).rank ≤ 8 := by
    simp only [tc88A, map_add]
    exact rank_add_le_of (rank_add_le_of (rank_add_le_of (rank_add_le_of
      (rank_add_le_of (rank_add_le_of (rank_add_le_of
      (vmvZ_rank_le _ _ K) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K))
      (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)
  have hB : ((Int.castRingHom K).mapMatrix tc88B).rank ≤ 8 := by
    simp only [tc88B, map_add]
    exact rank_add_le_of (rank_add_le_of (rank_add_le_of (rank_add_le_of
      (rank_add_le_of (rank_add_le_of (rank_add_le_of
      (vmvZ_rank_le _ _ K) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K))
      (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)) (vmvZ_rank_le _ _ K)
  omega

/-! ### Exact ±1 pole-order-2 border decomposition for `bTC_K(4, 4) ≤ 6` (ranks 3 + 3) -/

def b44A0u0 : Fin 4 × Fin 4 → ℤ := fun p => if p = (1, 0) then 1 else 0
def b44A0v0 : Fin 4 × Fin 4 → ℤ := fun p => if p = (3, 3) then -1 else 0
def b44A0u1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 2) then 1 else 0
def b44A0v1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 1) then -1 else 0
def b44A0u2 : Fin 4 × Fin 4 → ℤ := fun p => if p = (3, 3) then -1 else 0
def b44A0v2 : Fin 4 × Fin 4 → ℤ := fun p => if p = (1, 0) then 1 else 0
def b44A1u0 : Fin 4 × Fin 4 → ℤ := fun _ => 0
def b44A1v0 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 3) then 1 else 0
def b44A1u1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 1) then -1 else if p = (1, 2) then 1 else 0
def b44A1v1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 1) then -1 else if p = (1, 2) then 1 else 0
def b44A1u2 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 3) then 1 else 0
def b44A1v2 : Fin 4 × Fin 4 → ℤ := fun _ => 0
def b44A2u0 : Fin 4 × Fin 4 → ℤ := fun _ => 0
def b44A2v0 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 2) then -1 else if p = (3, 1) then 1 else 0
def b44A2u1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 0) then 1 else 0
def b44A2v1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 0) then 1 else 0
def b44A2u2 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 2) then -1 else if p = (3, 1) then 1 else 0
def b44A2v2 : Fin 4 × Fin 4 → ℤ := fun _ => 0
def b44B0u0 : Fin 4 × Fin 4 → ℤ := fun p => if p = (1, 3) then 1 else 0
def b44B0v0 : Fin 4 × Fin 4 → ℤ := fun p => if p = (3, 0) then 1 else 0
def b44B0u1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 1) then -1 else 0
def b44B0v1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 2) then -1 else 0
def b44B0u2 : Fin 4 × Fin 4 → ℤ := fun p => if p = (3, 0) then 1 else 0
def b44B0v2 : Fin 4 × Fin 4 → ℤ := fun p => if p = (1, 3) then 1 else 0
def b44B1u0 : Fin 4 × Fin 4 → ℤ := fun _ => 0
def b44B1v0 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 1) then 1 else if p = (3, 2) then 1 else 0
def b44B1u1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 3) then 1 else 0
def b44B1v1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 3) then 1 else 0
def b44B1u2 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 1) then 1 else if p = (3, 2) then 1 else 0
def b44B1v2 : Fin 4 × Fin 4 → ℤ := fun _ => 0
def b44B2u0 : Fin 4 × Fin 4 → ℤ := fun _ => 0
def b44B2v0 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 0) then 1 else 0
def b44B2u1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 2) then 1 else if p = (1, 1) then 1 else 0
def b44B2v1 : Fin 4 × Fin 4 → ℤ := fun p => if p = (0, 2) then 1 else if p = (1, 1) then 1 else 0
def b44B2u2 : Fin 4 × Fin 4 → ℤ := fun p => if p = (2, 0) then 1 else 0
def b44B2v2 : Fin 4 × Fin 4 → ℤ := fun _ => 0

/-- Coefficient of `ε^(m - 2)` on the A side of the `4 × 4` border decomposition. -/
def b44CA (m : ℕ) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℤ :=
  match m with
  | 0 => vmvZ b44A0u0 b44A0v0 + vmvZ b44A1u0 b44A1v0 + vmvZ b44A2u0 b44A2v0
  | 1 => vmvZ b44A0u0 b44A0v1 + vmvZ b44A0u1 b44A0v0 + vmvZ b44A1u0 b44A1v1 + vmvZ b44A1u1 b44A1v0 +
         vmvZ b44A2u0 b44A2v1 + vmvZ b44A2u1 b44A2v0
  | _ => vmvZ b44A0u0 b44A0v2 + vmvZ b44A0u1 b44A0v1 + vmvZ b44A0u2 b44A0v0 +
         vmvZ b44A1u0 b44A1v2 + vmvZ b44A1u1 b44A1v1 + vmvZ b44A1u2 b44A1v0 +
         vmvZ b44A2u0 b44A2v2 + vmvZ b44A2u1 b44A2v1 + vmvZ b44A2u2 b44A2v0

/-- Coefficient of `ε^(m - 2)` on the B side of the `4 × 4` border decomposition. -/
def b44CB (m : ℕ) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℤ :=
  match m with
  | 0 => vmvZ b44B0u0 b44B0v0 + vmvZ b44B1u0 b44B1v0 + vmvZ b44B2u0 b44B2v0
  | 1 => vmvZ b44B0u0 b44B0v1 + vmvZ b44B0u1 b44B0v0 + vmvZ b44B1u0 b44B1v1 + vmvZ b44B1u1 b44B1v0 +
         vmvZ b44B2u0 b44B2v1 + vmvZ b44B2u1 b44B2v0
  | _ => vmvZ b44B0u0 b44B0v2 + vmvZ b44B0u1 b44B0v1 + vmvZ b44B0u2 b44B0v0 +
         vmvZ b44B1u0 b44B1v2 + vmvZ b44B1u1 b44B1v1 + vmvZ b44B1u2 b44B1v0 +
         vmvZ b44B2u0 b44B2v2 + vmvZ b44B2u1 b44B2v1 + vmvZ b44B2u2 b44B2v0

private theorem border44_order_m2 : ∀ p q : Fin 4 × Fin 4, (b44CA 0 + ptrZ (b44CB 0)) p q = 0 := by decide
private theorem border44_order_m1 : ∀ p q : Fin 4 × Fin 4, (b44CA 1 + ptrZ (b44CB 1)) p q = 0 := by decide
private theorem border44_order_0 : ∀ p q : Fin 4 × Fin 4,
    (b44CA 2 + ptrZ (b44CB 2)) p q = if p = q then 1 else 0 := by decide

/-- Pole-order-2 border decomposition `bTC_K(4, 4) ≤ 6` (ranks `3 + 3`) over every field `K`:
the `ε⁻²` and `ε⁻¹` coefficients of `P(ε) + Q(ε)^Γ` vanish, and the `ε⁰` coefficient is `1`. -/
theorem border44_identity_field (K : Type*) [Field K] :
    (b44CA 0).map (Int.cast : ℤ → K) + ptr ((b44CB 0).map (Int.cast : ℤ → K)) = 0 ∧
    (b44CA 1).map (Int.cast : ℤ → K) + ptr ((b44CB 1).map (Int.cast : ℤ → K)) = 0 ∧
    (b44CA 2).map (Int.cast : ℤ → K) + ptr ((b44CB 2).map (Int.cast : ℤ → K)) = 1 := by
  have hptr : ∀ M : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℤ,
      ptr (M.map (Int.cast : ℤ → K)) = (ptrZ M).map (Int.cast : ℤ → K) := fun _ => by ext p q; rfl
  refine ⟨?_, ?_, ?_⟩ <;> ext p q <;> rw [hptr] <;>
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.zero_apply, Matrix.one_apply, ← Int.cast_add]
  · rw [show (b44CA 0 p q + ptrZ (b44CB 0) p q) = (b44CA 0 + ptrZ (b44CB 0)) p q from rfl,
      border44_order_m2 p q, Int.cast_zero]
  · rw [show (b44CA 1 p q + ptrZ (b44CB 1) p q) = (b44CA 1 + ptrZ (b44CB 1)) p q from rfl,
      border44_order_m1 p q, Int.cast_zero]
  · rw [show (b44CA 2 p q + ptrZ (b44CB 2) p q) = (b44CA 2 + ptrZ (b44CB 2)) p q from rfl,
      border44_order_0 p q]
    split_ifs <;> simp

end IntegerSchemes

end PastaMath.TwoCutSoS
