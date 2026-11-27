-- SPDX-License-Identifier: Apache-2.0
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import PastaMath.TwoCutSoS.Defs

/-!
# Exact dictionary between PT-rank, two-cut rank, bilinear products, and sums of squares

Proves over an arbitrary field `K` (with `char K ≠ 2` and `√(-1) ∈ K` where indicated):
* `exists_sum_rank_one_eq` and `exists_mul_transpose_of_rank_le`: rank factorisations.
* `hasPTRank_iff_hasTwoCut`: Rossman–Zhu Lemma 3.5 for `d = 2` over every field.
* `prod_of_twoCut`: `β ≤ TC` over every field.
* `twoCut_of_sos`: `TC ≤ 2 σ` for fully symmetric matrices when `char K ≠ 2` (Rossman–Zhu Lemma 3.15).
* `twoCut_of_prod`: `TC ≤ 4 β` for fully symmetric matrices when `char K ≠ 2`.
* `sos_of_prod`: `σ ≤ 2 β` when `char K ≠ 2` and `∃ i : K, i ^ 2 = -1`.
* `sos_of_twoCut` and `sos_of_ptRank`: the repaired Rossman–Zhu Lemma 3.13,
  `SoS(Q_M) ≤ 2 · PT-rank(M)` for every matrix `M` when `char K ≠ 2` and `∃ i : K, i ^ 2 = -1`.
-/

namespace PastaMath.TwoCutSoS

open Matrix Finset

variable {K : Type*} [Field K]

/-- Every matrix `A : Matrix m n K` is a sum of `A.rank` rank-one outer products. -/
theorem exists_sum_rank_one_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n K) :
    ∃ u : Fin A.rank → (m → K), ∃ v : Fin A.rank → (n → K),
      (∀ l, (Matrix.vecMulVec (u l) (v l)).rank = 1) ∧
      ∑ l, Matrix.vecMulVec (u l) (v l) = A := by
  let R := LinearMap.range A.mulVecLin
  let b := Module.finBasis K R
  have hcard : Module.finrank K R = A.rank := rfl
  let e : Fin A.rank ≃ Fin (Module.finrank K R) := finCongr hcard.symm
  let u : Fin A.rank → (m → K) := fun l => (b (e l)).1
  let v : Fin A.rank → (n → K) := fun l j =>
    b.repr ⟨A.mulVec (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩ (e l)
  refine ⟨u, v, ?_, ?_⟩
  · intro l
    have hu : u l ≠ 0 := by
      intro h0
      exact b.ne_zero (e l) (Subtype.ext h0)
    have hv : v l ≠ 0 := by
      intro h0
      rcases (b (e l)).2 with ⟨x, hx⟩
      have hlin : (⟨A.mulVec x, ⟨x, rfl⟩⟩ : R) =
          ∑ j : n, x j • (⟨A.mulVec (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩ : R) := by
        apply Subtype.ext
        have hxsum : x = ∑ j : n, x j • Pi.single j (1 : K) := by
          ext j; simp [Finset.sum_apply, Pi.single_apply]
        conv_lhs => rw [hxsum]
        simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
        change A.mulVecLin (∑ j : n, x j • Pi.single j (1 : K)) = _
        simp only [map_sum, map_smul]; rfl
      have hcoord : b.repr ⟨A.mulVec x, ⟨x, rfl⟩⟩ (e l) = 1 := by
        have hEq : (⟨A.mulVec x, ⟨x, rfl⟩⟩ : R) = b (e l) := Subtype.ext hx
        rw [hEq, b.repr_self, Finsupp.single_eq_same]
      rw [hlin, map_sum] at hcoord
      have hzero : (∑ j : n, (b.repr (x j •
          (⟨A.mulVec (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩ : R))) (e l)) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        have hvj : v l j = 0 := congrFun h0 j
        dsimp only [v] at hvj
        rw [hvj, mul_zero]
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply] at hcoord
      exact one_ne_zero (hcoord.symm.trans hzero)
    have hle : (Matrix.vecMulVec (u l) (v l)).rank ≤ 1 := by
      have hfac : Matrix.vecMulVec (u l) (v l) =
          (Matrix.of fun i (_ : Fin 1) => u l i) * (Matrix.of fun (_ : Fin 1) j => v l j) := by
        ext i j; simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
      rw [hfac]
      calc _ ≤ (Matrix.of fun i (_ : Fin 1) => u l i).rank := Matrix.rank_mul_le_left _ _
        _ ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_width _
        _ = 1 := Fintype.card_fin 1
    have hne : Matrix.vecMulVec (u l) (v l) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
      intro h0
      have := congrFun (congrFun h0 i) j
      simp [Matrix.vecMulVec_apply] at this
      exact this.elim hi hj
    have hpos : 0 < (Matrix.vecMulVec (u l) (v l)).rank := by
      by_contra h0
      have hr0 : (Matrix.vecMulVec (u l) (v l)).rank = 0 := Nat.eq_zero_of_not_pos h0
      apply hne
      apply Matrix.toLin'.injective
      rw [map_zero]
      have hbot : LinearMap.range (Matrix.vecMulVec (u l) (v l)).mulVecLin = ⊥ :=
        Submodule.finrank_eq_zero.1 hr0
      apply LinearMap.ext
      intro x
      have hx : (Matrix.vecMulVec (u l) (v l)).mulVecLin x ∈ (⊥ : Submodule K (m → K)) := by
        rw [← hbot]; exact ⟨x, rfl⟩
      rw [Submodule.mem_bot] at hx
      exact hx
    omega
  · ext i j
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
    have hsum := b.sum_repr ⟨A.mulVec (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩
    have hval := congrFun (congrArg Subtype.val hsum) i
    simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul] at hval
    have hcol : A.mulVec (Pi.single j 1) i = A i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcol] at hval
    rw [← hval]
    refine Fintype.sum_equiv e _ _ fun l => ?_
    dsimp only [u, v]
    ring

/-- Factor a matrix of rank `≤ k` as `U * Vᵀ` with `k` columns. -/
theorem exists_mul_transpose_of_rank_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n K) {k : ℕ} (hk : A.rank ≤ k) :
    ∃ (U : Matrix m (Fin k) K) (V : Matrix n (Fin k) K), U * Vᵀ = A := by
  obtain ⟨u, v, _, hsum⟩ := exists_sum_rank_one_eq A
  let U : Matrix m (Fin k) K := Matrix.of fun i t =>
    if h : t.1 < A.rank then u ⟨t.1, h⟩ i else 0
  let V : Matrix n (Fin k) K := Matrix.of fun j t =>
    if h : t.1 < A.rank then v ⟨t.1, h⟩ j else 0
  refine ⟨U, V, ?_⟩
  ext i j
  rw [← hsum]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, U, V]
  have hterm : ∀ t : Fin k,
      (if h : t.1 < A.rank then u ⟨t.1, h⟩ i else 0) *
        (if h : t.1 < A.rank then v ⟨t.1, h⟩ j else 0) =
      if h : t.1 < A.rank then u ⟨t.1, h⟩ i * v ⟨t.1, h⟩ j else 0 := by
    intro t; split_ifs <;> simp
  simp_rw [hterm]
  rw [← Finset.sum_subset (Finset.filter_subset (fun t : Fin k => t.1 < A.rank) Finset.univ)]
  · symm
    refine Finset.sum_bij (fun (l : Fin A.rank) _ => (⟨l.1, lt_of_lt_of_le l.2 hk⟩ : Fin k))
      ?_ ?_ ?_ ?_
    · intro l _; simp [l.2]
    · intro l₁ _ l₂ _ h
      exact Fin.ext (Fin.mk.inj h)
    · intro t ht
      rw [Finset.mem_filter] at ht
      exact ⟨⟨t.1, ht.2⟩, Finset.mem_univ _, rfl⟩
    · intro l _; simp [l.2]
  · intro t _ ht
    rw [Finset.mem_filter] at ht
    have hnt : ¬ (t.1 < A.rank) := fun h => ht ⟨Finset.mem_univ t, h⟩
    simp [hnt]

section Dictionary

variable {r s : ℕ}

/-- Rossman–Zhu Lemma 3.5 for `d = 2`: PT-rank coincides with two-cut rank over every field `K`. -/
theorem hasPTRank_iff_hasTwoCut (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (c : ℕ) :
    HasPTRank M c ↔ HasTwoCut M c := by
  classical
  constructor
  · rintro ⟨k, B, hkc, hB, hsum⟩
    let SA : Finset (Fin k) := Finset.univ.filter fun i => (B i).rank = 1
    let SB : Finset (Fin k) := Finset.univ.filter fun i => (B i).rank ≠ 1
    let A := ∑ i ∈ SA, B i
    let W := ∑ i ∈ SB, ptr (B i)
    refine ⟨A, W, ?_, ?_⟩
    · have hptrW : ptr W = ∑ i ∈ SB, B i := by
        dsimp only [W]; rw [ptr_sum]; refine Finset.sum_congr rfl fun i _ => ptr_ptr (B i)
      rw [hptrW, ← hsum]
      dsimp only [A, SA, SB]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => (B i).rank = 1) B
    · have hA : A.rank ≤ SA.card := by
        calc A.rank ≤ ∑ i ∈ SA, (B i).rank := rank_sum_le' SA B
          _ = ∑ _i ∈ SA, 1 := Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2
          _ = SA.card := by simp
      have hW : W.rank ≤ SB.card := by
        calc W.rank ≤ ∑ i ∈ SB, (ptr (B i)).rank := rank_sum_le' SB (fun i => ptr (B i))
          _ = ∑ _i ∈ SB, 1 := Finset.sum_congr rfl fun i hi => by
              have hne : (B i).rank ≠ 1 := (Finset.mem_filter.1 hi).2
              exact (hB i).resolve_left hne
          _ = SB.card := by simp
      have hcard : SA.card + SB.card = k := by
        dsimp only [SA, SB]
        simpa [Fintype.card_fin] using
          Finset.card_filter_add_card_filter_not (s := Finset.univ)
            (p := fun i : Fin k => (B i).rank = 1)
      omega
  · rintro ⟨A, W, hAW, hrk⟩
    obtain ⟨uA, vA, hA1, hAsum⟩ := exists_sum_rank_one_eq A
    obtain ⟨uW, vW, hW1, hWsum⟩ := exists_sum_rank_one_eq W
    let e : Fin A.rank ⊕ Fin W.rank ≃ Fin (A.rank + W.rank) := finSumFinEquiv
    let B : Fin (A.rank + W.rank) → Matrix (Fin r × Fin s) (Fin r × Fin s) K := fun i =>
      match e.symm i with
      | Sum.inl l => Matrix.vecMulVec (uA l) (vA l)
      | Sum.inr l => ptr (Matrix.vecMulVec (uW l) (vW l))
    refine ⟨A.rank + W.rank, B, hrk, ?_, ?_⟩
    · intro i
      dsimp only [B]
      cases h : e.symm i with
      | inl l => exact Or.inl (hA1 l)
      | inr l => exact Or.inr (by rw [ptr_ptr]; exact hW1 l)
    · rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
      have h1 : ∀ l : Fin A.rank, B (e (Sum.inl l)) = Matrix.vecMulVec (uA l) (vA l) := by
        intro l; simp [B]
      have h2 : ∀ l : Fin W.rank, B (e (Sum.inr l)) = ptr (Matrix.vecMulVec (uW l) (vW l)) := by
        intro l; simp [B]
      simp_rw [h1, h2]
      rw [hAsum, ← ptr_sum, hWsum, hAW]

/-- `β_K(M) ≤ TC_K(M)` over every field `K`. -/
theorem prod_of_twoCut (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) {c : ℕ}
    (h : HasTwoCut M c) : HasProdFormula M c := by
  classical
  rcases h with ⟨A, W, hAW, hrk⟩
  obtain ⟨uA, vA, _, hAsum⟩ := exists_sum_rank_one_eq A
  obtain ⟨uW, vW, _, hWsum⟩ := exists_sum_rank_one_eq W
  let u : Fin c → Fin r × Fin s → K := fun t =>
    if h1 : t.1 < A.rank then uA ⟨t.1, h1⟩
    else if h2 : t.1 - A.rank < W.rank then uW ⟨t.1 - A.rank, h2⟩
    else 0
  let v : Fin c → Fin r × Fin s → K := fun t =>
    if h1 : t.1 < A.rank then vA ⟨t.1, h1⟩
    else if h2 : t.1 - A.rank < W.rank then vW ⟨t.1 - A.rank, h2⟩
    else 0
  refine ⟨u, v, ?_⟩
  have hsplit : ∑ t : Fin c, Matrix.vecMulVec (u t) (v t) = A + W := by
    have hpart : (Finset.univ : Finset (Fin c)) =
        (Finset.univ.filter fun t : Fin c => t.1 < A.rank) ∪
        ((Finset.univ.filter fun t : Fin c => A.rank ≤ t.1 ∧ t.1 < A.rank + W.rank) ∪
         (Finset.univ.filter fun t : Fin c => A.rank + W.rank ≤ t.1)) := by
      ext t; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]; omega
    have hd1 : Disjoint (Finset.univ.filter fun t : Fin c => t.1 < A.rank)
        ((Finset.univ.filter fun t : Fin c => A.rank ≤ t.1 ∧ t.1 < A.rank + W.rank) ∪
         (Finset.univ.filter fun t : Fin c => A.rank + W.rank ≤ t.1)) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
      omega
    have hd2 : Disjoint
        (Finset.univ.filter fun t : Fin c => A.rank ≤ t.1 ∧ t.1 < A.rank + W.rank)
        (Finset.univ.filter fun t : Fin c => A.rank + W.rank ≤ t.1) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
      omega
    rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
    have hS1 : ∑ t ∈ Finset.univ.filter (fun t : Fin c => t.1 < A.rank),
        Matrix.vecMulVec (u t) (v t) = A := by
      conv_rhs => rw [← hAsum]
      symm
      refine Finset.sum_bij (fun (l : Fin A.rank) _ => (⟨l.1, by omega⟩ : Fin c))
        ?_ ?_ ?_ ?_
      · intro l _; simp [l.2]
      · intro l₁ _ l₂ _ heq
        exact Fin.ext (Fin.mk.inj heq)
      · intro t ht; rw [Finset.mem_filter] at ht; exact ⟨⟨t.1, ht.2⟩, Finset.mem_univ _, rfl⟩
      · intro l _; simp [u, v, l.2]
    have hS2 : ∑ t ∈ Finset.univ.filter (fun t : Fin c => A.rank ≤ t.1 ∧ t.1 < A.rank + W.rank),
        Matrix.vecMulVec (u t) (v t) = W := by
      conv_rhs => rw [← hWsum]
      symm
      refine Finset.sum_bij (fun (l : Fin W.rank) _ => (⟨A.rank + l.1, by omega⟩ : Fin c))
        ?_ ?_ ?_ ?_
      · intro l _; simp
      · intro l₁ _ l₂ _ heq
        have hval : A.rank + l₁.1 = A.rank + l₂.1 := congrArg Fin.val heq
        exact Fin.ext (by omega)
      · intro t ht
        rw [Finset.mem_filter] at ht
        refine ⟨⟨t.1 - A.rank, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
      · intro l _
        have h1 : ¬ (A.rank + l.1 < A.rank) := by omega
        simp [u, v, h1]
    have hS3 : ∑ t ∈ Finset.univ.filter (fun t : Fin c => A.rank + W.rank ≤ t.1),
        Matrix.vecMulVec (u t) (v t) = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [Finset.mem_filter] at ht
      have h1 : ¬ (t.1 < A.rank) := by omega
      have h2 : ¬ (t.1 - A.rank < W.rank) := by omega
      ext p q; simp [u, v, h1, h2, Matrix.vecMulVec_apply]
    rw [hS1, hS2, hS3, add_zero]
  rw [hsplit]
  unfold SameBiquad
  rw [← hAW, sym4_add, sym4_add, sym4_ptr]

/-- `TC_K(M) ≤ 2 σ_K(M)` for fully symmetric `M` when `char K ≠ 2` (Rossman–Zhu Lemma 3.15, `d = 2`). -/
theorem twoCut_of_sos (h2 : (2 : K) ≠ 0) (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (hM : IsFullySym M) {n : ℕ} (h : HasSoSFormula M n) : HasTwoCut M (2 * n) := by
  rcases h with ⟨L, hL⟩
  have hsymL : (Lᵀ * L)ᵀ = Lᵀ * L := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hsum : (Lᵀ * L) + ptr (Lᵀ * L) = (2 : K) • M := by
    have h4 : sym4 (Lᵀ * L) = (4 : K) • M := by
      rw [hL, sym4_of_isFullySym hM]
    have hL4 : sym4 (Lᵀ * L) = (2 : K) • ((Lᵀ * L) + ptr (Lᵀ * L)) := by
      unfold sym4
      rw [hsymL, ← ptr_transpose, hsymL]
      ext p q; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [hL4] at h4
    ext p q
    have hpq := congrFun (congrFun h4 p) q
    simp only [Matrix.smul_apply, smul_eq_mul] at hpq ⊢
    have : (2 : K) * ((Lᵀ * L + ptr (Lᵀ * L)) p q) = (2 : K) * (2 * M p q) := by
      linear_combination hpq
    exact mul_left_cancel₀ h2 this
  let S := (2⁻¹ : K) • (Lᵀ * L)
  refine ⟨S, S, ?_, ?_⟩
  · dsimp only [S]
    rw [ptr_smul, ← smul_add, hsum, smul_smul, inv_mul_cancel₀ h2, one_smul]
  · have hrk : S.rank ≤ n := by
      calc S.rank ≤ (Lᵀ * L).rank := rank_smul_le _ _
        _ ≤ L.rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_height _
        _ = n := Fintype.card_fin n
    omega

/-- `TC_K(M) ≤ 4 β_K(M)` for fully symmetric `M` when `char K ≠ 2`. -/
theorem twoCut_of_prod (h2 : (2 : K) ≠ 0) (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (hM : IsFullySym M) {n : ℕ} (h : HasProdFormula M n) : HasTwoCut M (4 * n) := by
  classical
  rcases h with ⟨u, v, hG⟩
  set G := ∑ l : Fin n, Matrix.vecMulVec (u l) (v l)
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  let S := (4⁻¹ : K) • (G + Gᵀ)
  refine ⟨S, S, ?_, ?_⟩
  · have hsum : (G + Gᵀ) + ptr (G + Gᵀ) = (4 : K) • M := by
      have hsym4 : sym4 G = (4 : K) • M := by rw [hG, sym4_of_isFullySym hM]
      unfold sym4 at hsym4
      rw [ptr_add, ptr_transpose, ← hsym4]
      abel
    dsimp only [S]
    rw [ptr_smul, ← smul_add, hsum, smul_smul, inv_mul_cancel₀ h4, one_smul]
  · have hGrk : G.rank ≤ n := by
      calc G.rank ≤ ∑ l : Fin n, (Matrix.vecMulVec (u l) (v l)).rank := rank_sum_le' _ _
        _ ≤ ∑ _l : Fin n, 1 := Finset.sum_le_sum fun l _ => by
            have hfac : Matrix.vecMulVec (u l) (v l) =
                (Matrix.of fun p (_ : Fin 1) => u l p) * (Matrix.of fun (_ : Fin 1) q => v l q) := by
              ext p q; simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
            rw [hfac]
            calc _ ≤ (Matrix.of fun p (_ : Fin 1) => u l p).rank := Matrix.rank_mul_le_left _ _
              _ ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_width _
              _ = 1 := Fintype.card_fin 1
        _ = n := by simp
    have hGT : Gᵀ.rank ≤ n := by rw [Matrix.rank_transpose]; exact hGrk
    have hSrk : S.rank ≤ 2 * n := by
      calc S.rank ≤ (G + Gᵀ).rank := rank_smul_le _ _
        _ ≤ G.rank + Gᵀ.rank := rank_add_le' G Gᵀ
        _ ≤ 2 * n := by omega
    omega

/-- `σ_K(M) ≤ 2 β_K(M)` when `char K ≠ 2` and `K` contains a square root of `-1`. -/
theorem sos_of_prod (h2 : (2 : K) ≠ 0) {I : K} (hI : I ^ 2 = -1)
    (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) {n : ℕ}
    (h : HasProdFormula M n) : HasSoSFormula M (2 * n) := by
  rcases h with ⟨u, v, huv⟩
  let e : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
    finSumFinEquiv.trans (finCongr (by omega))
  let L : Matrix (Fin (2 * n)) (Fin r × Fin s) K := Matrix.of fun k p =>
    match e.symm k with
    | Sum.inl l => (2⁻¹ : K) * (u l p + v l p)
    | Sum.inr l => (2⁻¹ : K) * I * (u l p - v l p)
  refine ⟨L, ?_⟩
  rw [sameBiquad_iff_qf h2]
  intro x y
  rw [qf_gram, ← Equiv.sum_comp e, Fintype.sum_sum_type]
  have h1 : ∀ l : Fin n,
      (∑ p, L (e (Sum.inl l)) p * (x p.1 * y p.2)) ^ 2 +
      (∑ p, L (e (Sum.inr l)) p * (x p.1 * y p.2)) ^ 2 =
      (∑ p, u l p * (x p.1 * y p.2)) * (∑ q, v l q * (x q.1 * y q.2)) := by
    intro l
    set U := ∑ p, u l p * (x p.1 * y p.2)
    set V := ∑ p, v l p * (x p.1 * y p.2)
    have hL1 : ∑ p, L (e (Sum.inl l)) p * (x p.1 * y p.2) = (2⁻¹ : K) * (U + V) := by
      simp only [L, Matrix.of_apply, Equiv.symm_apply_apply, U, V]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    have hL2 : ∑ p, L (e (Sum.inr l)) p * (x p.1 * y p.2) = (2⁻¹ : K) * I * (U - V) := by
      simp only [L, Matrix.of_apply, Equiv.symm_apply_apply, U, V]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hL1, hL2]
    have h2inv : (2⁻¹ : K) * 2 = 1 := inv_mul_cancel₀ h2
    have h4inv : (2⁻¹ : K) ^ 2 * 4 = 1 := by
      calc (2⁻¹ : K) ^ 2 * 4 = ((2⁻¹ : K) * 2) * ((2⁻¹ : K) * 2) := by ring
        _ = 1 * 1 := by rw [h2inv]
        _ = 1 := one_mul 1
    calc ((2⁻¹ : K) * (U + V)) ^ 2 + ((2⁻¹ : K) * I * (U - V)) ^ 2
        = (2⁻¹ : K) ^ 2 * ((U + V) ^ 2 + I ^ 2 * (U - V) ^ 2) := by ring
      _ = (2⁻¹ : K) ^ 2 * ((U + V) ^ 2 + (-1) * (U - V) ^ 2) := by rw [hI]
      _ = ((2⁻¹ : K) ^ 2 * 4) * (U * V) := by ring
      _ = U * V := by rw [h4inv, one_mul]
  rw [← Finset.sum_add_distrib]
  simp_rw [h1]
  have hq := (sameBiquad_iff_qf h2 _ _).1 huv x y
  rw [qf_sum] at hq
  simpa [qf_vecMulVec] using hq

/-- Repaired Rossman–Zhu Lemma 3.13 (in two-cut form):
for every matrix `M` (not necessarily symmetric), `SoS(Q_M) ≤ 2 · TC(M)` whenever
`char K ≠ 2` and `√(-1) ∈ K`. -/
theorem sos_of_twoCut (h2 : (2 : K) ≠ 0) {I : K} (hI : I ^ 2 = -1)
    (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) {c : ℕ}
    (h : HasTwoCut M c) : HasSoSFormula M (2 * c) :=
  sos_of_prod h2 hI M (prod_of_twoCut M h)

/-- Repaired Rossman–Zhu Lemma 3.13 (in PT-rank form):
for every matrix `M`, `SoS(Q_M) ≤ 2 · PT-rank(M)` whenever `char K ≠ 2` and `√(-1) ∈ K`. -/
theorem sos_of_ptRank (h2 : (2 : K) ≠ 0) {I : K} (hI : I ^ 2 = -1)
    (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) {c : ℕ}
    (h : HasPTRank M c) : HasSoSFormula M (2 * c) :=
  sos_of_twoCut h2 hI M ((hasPTRank_iff_hasTwoCut M c).1 h)

/-- Crossing dictionary: `β_K(r, s) ≤ TC_K(r, s)` over every field `K`. -/
theorem crossing_prod_of_twoCut {c : ℕ}
    (h : HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) c) :
    HasProdFormula (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) c :=
  prod_of_twoCut 1 h

/-- Crossing dictionary: `TC_K(r, s) ≤ 2 σ_K(r, s)` when `char K ≠ 2`. -/
theorem crossing_twoCut_of_sos (h2 : (2 : K) ≠ 0) {n : ℕ}
    (h : HasSoSFormula (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) n) :
    HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (2 * n) :=
  twoCut_of_sos h2 1 isFullySym_one h

/-- Crossing dictionary: `TC_K(r, s) ≤ 4 β_K(r, s)` when `char K ≠ 2`. -/
theorem crossing_twoCut_of_prod (h2 : (2 : K) ≠ 0) {n : ℕ}
    (h : HasProdFormula (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) n) :
    HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (4 * n) :=
  twoCut_of_prod h2 1 isFullySym_one h

/-- Crossing dictionary: `σ_K(r, s) ≤ 2 TC_K(r, s)` when `char K ≠ 2` and `√(-1) ∈ K`. -/
theorem crossing_sos_of_twoCut (h2 : (2 : K) ≠ 0) {I : K} (hI : I ^ 2 = -1) {c : ℕ}
    (h : HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) c) :
    HasSoSFormula (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (2 * c) :=
  sos_of_twoCut h2 hI 1 h

end Dictionary

end PastaMath.TwoCutSoS
