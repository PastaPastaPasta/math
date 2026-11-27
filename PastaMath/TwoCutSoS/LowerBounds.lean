-- SPDX-License-Identifier: Apache-2.0
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
import Mathlib.Tactic.NormNum
import PastaMath.TwoCutSoS.Dictionary

/-!
# Characteristic-free exact lower and upper bounds for the crossing two-cut rank

Proves over **every** field `K` (including characteristic `2`):
* `twoCut_ge_max`: `TC_K(r, s) ≥ max r s`.
* `twoCut_swap`: `TC_K(r, s) = TC_K(s, r)`.
* `twoCut_gt_max_of_ge_three`: `TC_K(r, s) ≥ max r s + 1` whenever `r ≥ 3` and `s ≥ 3`,
  over every field (including characteristic 2).
* `twoCut_two_iff`: `TC_K(2, s) = 2 * ⌈s / 2⌉` for every `s`, over every field.
* `transpose_twoCut`: `TC_K(r, s) ≤ 1 + r * s - min r s * (min r s + 1) / 2` over every field.
* `twoCut_three_three_iff`: `TC_K(3, 3) = 4` over every field.
-/

namespace PastaMath.TwoCutSoS

open Matrix Finset

variable {K : Type*} [Field K]

/-- Complementary idempotents: if `A + B = 1` and `rank A + rank B ≤ n`, then
`A² = A`, `AB = 0`, `BA = 0`, and `rank A + rank B = n`. -/
theorem idem_of_add_eq_one {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (h : A + B = 1)
    (hr : A.rank + B.rank ≤ n) : A * A = A ∧ A * B = 0 ∧ B * A = 0 ∧ A.rank + B.rank = n := by
  set RA := LinearMap.range A.mulVecLin
  set RB := LinearMap.range B.mulVecLin
  have hsup : RA ⊔ RB = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = A.mulVec v + B.mulVec v := by
      rw [← Matrix.add_mulVec, h, Matrix.one_mulVec]
    rw [hv]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq RA RB
  rw [hsup, finrank_top, Module.finrank_fin_fun] at hdim
  have hinf : Module.finrank K (RA ⊓ RB : Submodule K (Fin n → K)) = 0 := by
    have : Module.finrank K RA + Module.finrank K RB ≤ n := hr
    omega
  have heq : A.rank + B.rank = n := by
    have : Module.finrank K RA + Module.finrank K RB = n := by omega
    exact this
  have hbot : RA ⊓ RB = ⊥ := Submodule.finrank_eq_zero.mp hinf
  have hAB : A * B = B * A := by
    have hB : B = 1 - A := by rw [← h]; abel
    rw [hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  have hzero : A * B = 0 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have h1 : (A * B).mulVec v ∈ RA := by
      rw [← Matrix.mulVec_mulVec]; exact ⟨B.mulVec v, rfl⟩
    have h2 : (A * B).mulVec v ∈ RB := by
      rw [hAB, ← Matrix.mulVec_mulVec]; exact ⟨A.mulVec v, rfl⟩
    have h3 : (A * B).mulVec v ∈ RA ⊓ RB := ⟨h1, h2⟩
    rw [hbot] at h3
    simpa [Matrix.toLin'_apply] using h3
  refine ⟨?_, hzero, hAB ▸ hzero, heq⟩
  have hB : B = 1 - A := by rw [← h]; abel
  have : A * (1 - A) = 0 := hB ▸ hzero
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  exact this.symm

/-- Number of upper-triangular pairs `(i, j)` in `Fin n × Fin n` with `i ≤ j`:
`2 * card { p : Fin n × Fin n // p.1 ≤ p.2 } = n * (n + 1)`. -/
private lemma card_upper_pairs (n : ℕ) :
    2 * Fintype.card { p : Fin n × Fin n // p.1 ≤ p.2 } = n * (n + 1) := by
  classical
  have hbij : Fintype.card { p : Fin n × Fin n // p.1 ≤ p.2 } +
      Fintype.card { p : Fin n × Fin n // p.2 < p.1 } = Fintype.card (Fin n × Fin n) := by
    have h1 := Fintype.card_subtype_compl (fun p : Fin n × Fin n => p.1 ≤ p.2)
    have hle := Fintype.card_subtype_le (fun p : Fin n × Fin n => p.1 ≤ p.2)
    have heq : Fintype.card { p : Fin n × Fin n // ¬ p.1 ≤ p.2 } =
        Fintype.card { p : Fin n × Fin n // p.2 < p.1 } :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun _ => not_le)
    omega
  have hdiag : Fintype.card { p : Fin n × Fin n // p.1 ≤ p.2 } =
      Fintype.card { p : Fin n × Fin n // p.1 = p.2 } +
      Fintype.card { p : Fin n × Fin n // p.1 < p.2 } := by
    have hdisj : Disjoint
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2)
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
    have hunion : (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2) =
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2) ∪
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      exact le_iff_eq_or_lt
    simp only [Fintype.card_subtype]
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hswap : Fintype.card { p : Fin n × Fin n // p.2 < p.1 } =
      Fintype.card { p : Fin n × Fin n // p.1 < p.2 } :=
    Fintype.card_congr
      { toFun := fun ⟨p, hp⟩ => ⟨p.swap, hp⟩
        invFun := fun ⟨p, hp⟩ => ⟨p.swap, hp⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  have hdiag_card : Fintype.card { p : Fin n × Fin n // p.1 = p.2 } = n := by
    have he : { p : Fin n × Fin n // p.1 = p.2 } ≃ Fin n :=
      { toFun := fun ⟨p, _⟩ => p.1
        invFun := fun i => ⟨(i, i), rfl⟩
        left_inv := fun ⟨⟨i, j⟩, h⟩ => by cases h; rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr he, Fintype.card_fin]
  have htot : Fintype.card (Fin n × Fin n) = n * n := by simp
  have hnn : n * (n + 1) = n * n + n := by ring
  omega

/-- Slice lower bound: `r ≤ TC_K(r, s)` when `s ≥ 1`, and `s ≤ TC_K(r, s)` when `r ≥ 1`,
so `max r s ≤ TC_K(r, s)` whenever `r ≥ 1` and `s ≥ 1`. -/
theorem twoCut_ge_left {r s c : ℕ} (hs : 0 < s)
    (h : HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) c) : r ≤ c := by
  rcases h with ⟨A, W, hAW, hrk⟩
  let b₀ : Fin s := ⟨0, hs⟩
  let f : Fin r → Fin r × Fin s := fun a => (a, b₀)
  have hsub : A.submatrix f f + W.submatrix f f = 1 := by
    ext a c'
    have := congrFun (congrFun hAW (a, b₀)) (c', b₀)
    simpa [f, Matrix.submatrix_apply, Matrix.add_apply, ptr_apply, Matrix.one_apply] using this
  have h1 : r = (1 : Matrix (Fin r) (Fin r) K).rank := by simp
  calc r = (A.submatrix f f + W.submatrix f f).rank := by rw [hsub]; exact h1
    _ ≤ (A.submatrix f f).rank + (W.submatrix f f).rank := rank_add_le' _ _
    _ ≤ A.rank + W.rank := add_le_add (Matrix.rank_submatrix_le _ _ _) (Matrix.rank_submatrix_le _ _ _)
    _ ≤ c := hrk

theorem twoCut_ge_right {r s c : ℕ} (hr : 0 < r)
    (h : HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) c) : s ≤ c := by
  rcases h with ⟨A, W, hAW, hrk⟩
  let a₀ : Fin r := ⟨0, hr⟩
  let f : Fin s → Fin r × Fin s := fun b => (a₀, b)
  have hsub : A.submatrix f f + (W.submatrix f f)ᵀ = 1 := by
    ext b d
    have := congrFun (congrFun hAW (a₀, b)) (a₀, d)
    simpa [f, Matrix.submatrix_apply, Matrix.add_apply, ptr_apply, Matrix.transpose_apply,
      Matrix.one_apply] using this
  have h1 : s = (1 : Matrix (Fin s) (Fin s) K).rank := by simp
  calc s = (A.submatrix f f + (W.submatrix f f)ᵀ).rank := by rw [hsub]; exact h1
    _ ≤ (A.submatrix f f).rank + (W.submatrix f f)ᵀ.rank := rank_add_le' _ _
    _ = (A.submatrix f f).rank + (W.submatrix f f).rank := by rw [Matrix.rank_transpose]
    _ ≤ A.rank + W.rank := add_le_add (Matrix.rank_submatrix_le _ _ _) (Matrix.rank_submatrix_le _ _ _)
    _ ≤ c := hrk

theorem twoCut_ge_max {r s c : ℕ} (hr : 0 < r) (hs : 0 < s)
    (h : HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) c) : max r s ≤ c :=
  max_le (twoCut_ge_left hs h) (twoCut_ge_right hr h)

/-- Symmetry of the crossing two-cut rank in `(r, s)`. -/
theorem twoCut_swap {r s c : ℕ} :
    HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) c ↔
    HasTwoCut (1 : Matrix (Fin s × Fin r) (Fin s × Fin r) K) c := by
  have fwd : ∀ {r' s' : ℕ},
      HasTwoCut (1 : Matrix (Fin r' × Fin s') (Fin r' × Fin s') K) c →
      HasTwoCut (1 : Matrix (Fin s' × Fin r') (Fin s' × Fin r') K) c := by
    intro r' s' ⟨A, W, hAW, hrk⟩
    let sw : Fin s' × Fin r' → Fin r' × Fin s' := Prod.swap
    refine ⟨A.submatrix sw sw, (W.submatrix sw sw)ᵀ, ?_, ?_⟩
    · ext ⟨b, a⟩ ⟨d, c'⟩
      have := congrFun (congrFun hAW (a, b)) (c', d)
      simpa [sw, Matrix.submatrix_apply, Matrix.add_apply, ptr_apply, Matrix.transpose_apply,
        Matrix.one_apply, Prod.mk.injEq, and_comm] using this
    · calc (A.submatrix sw sw).rank + (W.submatrix sw sw)ᵀ.rank
          = (A.submatrix sw sw).rank + (W.submatrix sw sw).rank := by rw [Matrix.rank_transpose]
        _ ≤ A.rank + W.rank :=
          add_le_add (Matrix.rank_submatrix_le _ _ _) (Matrix.rank_submatrix_le _ _ _)
        _ ≤ c := hrk
  exact ⟨fwd, fwd⟩

/-- Counting step: `r * a ≤ s` and `2 * (r - 1) * s ≤ (r * r + r - 2) * a`
with `1 ≤ r` and `1 ≤ a` force `r ≤ 2`. -/
private lemma tcB_core {r a s : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a) (h1 : r * a ≤ s)
    (h2 : 2 * ((r - 1) * s) ≤ (r * r + r - 2) * a) : r ≤ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have e1 : k + 1 - 1 = k := by omega
  have e2 : (k + 1) * (k + 1) + (k + 1) - 2 = k * k + 3 * k := by
    have : (k + 1) * (k + 1) + (k + 1) = k * k + 3 * k + 2 := by ring
    omega
  rw [e1, e2] at h2
  by_contra hc
  have hk : 2 ≤ k := by omega
  have h3 : 2 * (k * ((k + 1) * a)) ≤ 2 * (k * s) := by
    have := Nat.mul_le_mul_left k h1; omega
  have h4 : 2 * (k * ((k + 1) * a)) ≤ (k * k + 3 * k) * a := le_trans h3 h2
  have h5 : (k * k + 3 * k) * a < 2 * (k * ((k + 1) * a)) := by
    have hpos : 0 < (k * k - k) * a := by
      apply Nat.mul_pos _ ha
      have : k < k * k := by nlinarith
      omega
    have expand : 2 * (k * ((k + 1) * a)) = (k * k + 3 * k) * a + (k * k - k) * a := by
      have hkk : k ≤ k * k := by nlinarith
      zify [hkk]; ring
    omega
  omega

/-- Key characteristic-free structural lemma: if `r ≥ 2`, `r ≤ s`, and `TC_K(r, s) ≤ s`,
then `r = 2` and `s` is even (in fact `s = 2 * a` where `a = rank A`). -/
private theorem twoCut_eq_max_forces_two_even {r s : ℕ} (hr : 2 ≤ r) (hrs : r ≤ s)
    (h : HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) s) :
    r = 2 ∧ Even s := by
  classical
  rcases h with ⟨A, W, hAW, hrk⟩
  set a := A.rank
  set b := W.rank
  -- First show `1 ≤ a` (if `a = 0` then `A = 0`, `W = 1`, `rank W = r * s > s`).
  have ha_pos : 1 ≤ a := by
    by_contra ha0
    have ha' : A.rank = 0 := by omega
    have hA0 : A = 0 := by
      apply Matrix.toLin'.injective
      rw [map_zero]
      have hbot : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 ha'
      apply LinearMap.ext
      intro x
      have hx : A.mulVecLin x ∈ (⊥ : Submodule K (Fin r × Fin s → K)) := by
        rw [← hbot]; exact ⟨x, rfl⟩
      rw [Submodule.mem_bot] at hx
      exact hx
    rw [hA0, zero_add] at hAW
    have hW1 : W = 1 := by
      have := congrArg ptr hAW
      rwa [ptr_ptr, ptr_one] at this
    have hWrk : W.rank = r * s := by rw [hW1]; simp
    have : r * s ≤ s := by omega
    nlinarith
  -- Factor `A = U * Vᵀ` with `U, V : Matrix (Fin r × Fin s) (Fin a) K`.
  obtain ⟨U, V, hUV⟩ := exists_mul_transpose_of_rank_le A (le_refl a)
  -- Block slices `U_i, V_i : Matrix (Fin s) (Fin a) K`.
  let Ublk : Fin r → Matrix (Fin s) (Fin a) K := fun i => Matrix.of fun β t => U (i, β) t
  let Vblk : Fin r → Matrix (Fin s) (Fin a) K := fun i => Matrix.of fun β t => V (i, β) t
  -- For any `x, φ : Fin r → K` with `dotProduct x φ = 1`, the contracted slice
  -- `P(x, φ) + Q(x, φ)ᵀ = 1` has `rank P ≤ a`, `rank Q ≤ b`, `a + b ≤ s`,
  -- so `P` is idempotent of rank `a`, which forces `V_φᵀ * U_x = 1`.
  have hslice_orth : ∀ (x φ : Fin r → K), dotProduct x φ = 1 →
      (∑ k : Fin r, φ k • Vblk k)ᵀ * (∑ i : Fin r, x i • Ublk i) = 1 := by
    intro x φ hxφ
    set Ux : Matrix (Fin s) (Fin a) K := ∑ i : Fin r, x i • Ublk i
    set Vφ : Matrix (Fin s) (Fin a) K := ∑ k : Fin r, φ k • Vblk k
    let P : Matrix (Fin s) (Fin s) K := Ux * Vφᵀ
    let Q : Matrix (Fin s) (Fin s) K :=
      Matrix.of fun β δ => ∑ i : Fin r, ∑ k : Fin r, x i * φ k * W (i, δ) (k, β)
    -- Show `P + Q = 1`.
    have hPQ : P + Q = 1 := by
      ext β δ
      have hP_entry : P β δ = ∑ i : Fin r, ∑ k : Fin r, x i * φ k * A (i, β) (k, δ) := by
        dsimp only [P, Ux, Vφ]
        rw [Matrix.transpose_sum, Matrix.sum_mul]
        simp only [Matrix.sum_apply, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.transpose_smul, Matrix.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        have hAik : A (i, β) (k, δ) = (Ublk i * (Vblk k)ᵀ) β δ := by
          rw [← hUV]
          simp [Matrix.mul_apply, Matrix.transpose_apply, Ublk, Vblk]
        rw [hAik]; ring
      simp only [Matrix.add_apply, hP_entry, Q, Matrix.of_apply]
      rw [← Finset.sum_add_distrib]
      have hcomb : ∀ i : Fin r,
          (∑ k : Fin r, x i * φ k * A (i, β) (k, δ)) +
          (∑ k : Fin r, x i * φ k * W (i, δ) (k, β)) =
          ∑ k : Fin r, x i * φ k * (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (i, β) (k, δ) := by
        intro i
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h1 := congrFun (congrFun hAW (i, β)) (k, δ)
        simp only [Matrix.add_apply, ptr_apply] at h1
        rw [← h1]; ring
      simp_rw [hcomb]
      have hdiag : ∀ i : Fin r,
          (∑ k : Fin r, x i * φ k *
            (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (i, β) (k, δ)) =
          x i * φ i * (1 : Matrix (Fin s) (Fin s) K) β δ := by
        intro i
        have hterm : ∀ k : Fin r,
            x i * φ k * (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (i, β) (k, δ) =
            if k = i then x i * φ i * (1 : Matrix (Fin s) (Fin s) K) β δ else 0 := by
          intro k
          by_cases hki : k = i
          · subst hki; by_cases hbd : β = δ <;> simp [Matrix.one_apply, hbd]
          · simp [Ne.symm hki, hki]
        simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp_rw [hdiag]
      rw [← Finset.sum_mul]
      change dotProduct x φ * (1 : Matrix (Fin s) (Fin s) K) β δ = _
      rw [hxφ, one_mul]
    -- `rank P ≤ a` and `rank Q ≤ b`.
    have hPrk : P.rank ≤ a := by
      calc P.rank ≤ Ux.rank := Matrix.rank_mul_le_left _ _
        _ ≤ Fintype.card (Fin a) := Matrix.rank_le_card_width _
        _ = a := Fintype.card_fin a
    have hQrk : Q.rank ≤ b := by
      let Lφ : Matrix (Fin s) (Fin r × Fin s) K :=
        Matrix.of fun β q => if q.2 = β then φ q.1 else 0
      let Rx : Matrix (Fin r × Fin s) (Fin s) K :=
        Matrix.of fun p δ => if p.2 = δ then x p.1 else 0
      have hQfac : Q = (Lφ * Wᵀ * Rx) := by
        ext β δ
        simp only [Q, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Lφ, Rx]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hsum1 : ∑ d : Fin s,
            (∑ p : Fin r × Fin s, (if p.2 = β then φ p.1 else 0) * W (i, d) p) *
              (if d = δ then x i else 0) =
            (∑ p : Fin r × Fin s, (if p.2 = β then φ p.1 else 0) * W (i, δ) p) * x i := by
          have : ∀ d : Fin s,
              (∑ p : Fin r × Fin s, (if p.2 = β then φ p.1 else 0) * W (i, d) p) *
                (if d = δ then x i else 0) =
              if d = δ then (∑ p : Fin r × Fin s, (if p.2 = β then φ p.1 else 0) * W (i, δ) p) * x i
              else 0 := by
            intro d; split_ifs with hd <;> simp [hd]
          simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hsum1, Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hsum2 : ∑ c : Fin s, (if c = β then φ k else 0) * W (i, δ) (k, c) =
            φ k * W (i, δ) (k, β) := by
          have : ∀ c : Fin s, (if c = β then φ k else 0) * W (i, δ) (k, c) =
              if c = β then φ k * W (i, δ) (k, β) else 0 := by
            intro c; split_ifs with hc <;> simp [hc]
          simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hsum2]; ring
      rw [hQfac]
      calc (Lφ * Wᵀ * Rx).rank ≤ (Lφ * Wᵀ).rank := Matrix.rank_mul_le_left _ _
        _ ≤ Wᵀ.rank := Matrix.rank_mul_le_right _ _
        _ = b := Matrix.rank_transpose W
    -- By `idem_of_add_eq_one`, `P * P = P` and `P.rank = a`.
    obtain ⟨hPidem, _, _, hPsum⟩ := idem_of_add_eq_one hPQ (by omega)
    have hPeq : P.rank = a := by omega
    -- `P = Ux * Vφᵀ` has rank `a`, so `Ux` is injective (`mulVecLin` injective) and `Vφᵀ` is surjective!
    have hUx_rk : Ux.rank = a := by
      have h1 : a ≤ Ux.rank := le_trans (le_of_eq hPeq.symm) (Matrix.rank_mul_le_left Ux Vφᵀ)
      have h2 : Ux.rank ≤ a := by
        simpa [Fintype.card_fin] using Matrix.rank_le_card_width Ux
      omega
    have hVφ_rk : Vφᵀ.rank = a := by
      have h1 : a ≤ Vφᵀ.rank := le_trans (le_of_eq hPeq.symm) (Matrix.rank_mul_le_right Ux Vφᵀ)
      have h2 : Vφᵀ.rank ≤ a := by
        simpa [Fintype.card_fin] using Matrix.rank_le_card_height Vφᵀ
      omega
    have hUx_inj : Function.Injective Ux.mulVecLin := by
      rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
      have hrn := LinearMap.finrank_range_add_finrank_ker Ux.mulVecLin
      rw [Module.finrank_fin_fun] at hrn
      change Ux.rank + Module.finrank K (LinearMap.ker Ux.mulVecLin) = a at hrn
      omega
    have hVφ_surj : Function.Surjective Vφᵀ.mulVecLin := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      exact hVφ_rk
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    obtain ⟨z, hz⟩ := hVφ_surj w
    apply hUx_inj
    have h1 : (Ux * (Vφᵀ * Ux) * Vφᵀ).mulVec z = (Ux * Vφᵀ).mulVec z := by
      have hassoc : Ux * (Vφᵀ * Ux) * Vφᵀ = P * P := by
        dsimp only [P]; simp only [Matrix.mul_assoc]
      rw [hassoc, hPidem]
    change Ux.mulVec ((Vφᵀ * Ux).mulVec w) = Ux.mulVec ((1 : Matrix (Fin a) (Fin a) K).mulVec w)
    rw [Matrix.one_mulVec, ← hz]
    change Ux.mulVec ((Vφᵀ * Ux).mulVec (Vφᵀ.mulVec z)) = Ux.mulVec (Vφᵀ.mulVec z)
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at h1 ⊢
    exact h1
  -- Specialise `hslice_orth` to `e_i, e_i` and `e_i, e_i + e_k` to get `V_kᵀ * U_i = δ_{ki} I_a`.
  have hVU : ∀ i k : Fin r, (Vblk k)ᵀ * Ublk i = if k = i then 1 else 0 := by
    intro i k
    let ei : Fin r → K := Pi.single i (1 : K)
    let ek : Fin r → K := Pi.single k (1 : K)
    have hii : (Vblk i)ᵀ * Ublk i = 1 := by
      have h := hslice_orth ei ei (by simp [ei, dotProduct, Pi.single_apply])
      have hU : ∑ j : Fin r, ei j • Ublk j = Ublk i := by simp [ei, Pi.single_apply]
      have hV : ∑ j : Fin r, ei j • Vblk j = Vblk i := by simp [ei, Pi.single_apply]
      rwa [hU, hV] at h
    by_cases hki : k = i
    · subst hki; simpa using hii
    · have hik : (Vblk i + Vblk k)ᵀ * Ublk i = 1 := by
        have hdot : dotProduct ei (ei + ek) = 1 := by
          simp [ei, ek, dotProduct, Pi.single_apply, Ne.symm hki]
        have h := hslice_orth ei (ei + ek) hdot
        have hU : ∑ j : Fin r, ei j • Ublk j = Ublk i := by simp [ei, Pi.single_apply]
        have hV : ∑ j : Fin r, (ei + ek) j • Vblk j = Vblk i + Vblk k := by
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ei, ek, Pi.single_apply]
          simp
        rwa [hU, hV] at h
      rw [Matrix.transpose_add, Matrix.add_mul, hii] at hik
      have h0 : (Vblk k)ᵀ * Ublk i = 0 := by
        have := congrArg (fun X => X - 1) hik
        simpa using this
      simp [hki, h0]
  -- Consequence 1: `r * a ≤ s`.
  have hra_le_s : r * a ≤ s := by
    let Uall : Matrix (Fin s) (Fin r × Fin a) K := Matrix.of fun β p => Ublk p.1 β p.2
    let Vall : Matrix (Fin r × Fin a) (Fin s) K := Matrix.of fun p β => Vblk p.1 β p.2
    have hprod : Vall * Uall = 1 := by
      ext ⟨k, t₁⟩ ⟨i, t₂⟩
      have h := congrFun (congrFun (hVU i k) t₁) t₂
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Vall, Uall] at h ⊢
      by_cases hki : k = i
      · subst hki; simp [Matrix.one_apply] at h ⊢; exact h
      · simp [hki] at h ⊢; exact h
    calc r * a = Fintype.card (Fin r × Fin a) := by simp
      _ = (1 : Matrix (Fin r × Fin a) (Fin r × Fin a) K).rank := by simp
      _ = (Vall * Uall).rank := by rw [hprod]
      _ ≤ Uall.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin s) := Matrix.rank_le_card_height _
      _ = s := Fintype.card_fin s
  -- Consequence 2: `dim ker(W) ≤ C(r+1, 2) * a` via the injective linear map
  -- `Ψ : ker(W) → {p : Fin r × Fin r // p.1 ≤ p.2} × Fin a → K`, `v ↦ ((U_kᵀ v_i)_t)`.
  let Upper := { p : Fin r × Fin r // p.1 ≤ p.2 }
  let Ψ : LinearMap.ker W.mulVecLin →ₗ[K] (Upper × Fin a → K) :=
    { toFun := fun v q => ∑ β : Fin s, Ublk q.1.1.1 β q.2 * v.1 (q.1.1.2, β)
      map_add' := fun v₁ v₂ => by
        ext ⟨⟨⟨k, i⟩, _⟩, t⟩
        simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        ext ⟨⟨⟨k, i⟩, _⟩, t⟩
        simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun β _ => by ring }
  -- Prove `Ψ` is injective!
  have hΨ_inj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    -- First, `v ∈ ker W` means `W * v = 0`. Since `W = 1 - ptr A`, `v = (ptr A) * v`.
    have hfix : ∀ (k : Fin r) (β : Fin s),
        v.1 (k, β) = ∑ i : Fin r, ∑ t : Fin a,
          Vblk i β t * (∑ α : Fin s, Ublk k α t * v.1 (i, α)) := by
      intro k β
      have hW_eq : W = 1 - ptr A := by
        have := congrArg ptr hAW
        rw [ptr_add, ptr_ptr, ptr_one] at this
        ext p q
        have hpq := congrFun (congrFun this p) q
        simp only [Matrix.add_apply, Matrix.sub_apply] at hpq ⊢
        linear_combination hpq
      have hW_mul : ((1 - ptr A).mulVec v.1) (k, β) = 0 := by
        have hv0 : W.mulVec v.1 = 0 := v.2
        have h1 : (1 - ptr A).mulVec v.1 = 0 := by rw [← hW_eq]; exact hv0
        exact congrFun h1 (k, β)
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at hW_mul
      rw [hW_mul]
      simp only [Matrix.mulVec, dotProduct, ptr_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hA_ent : ∀ α : Fin s,
          A (k, α) (i, β) = ∑ t : Fin a, Ublk k α t * Vblk i β t := by
        intro α
        rw [← hUV]
        simp [Matrix.mul_apply, Matrix.transpose_apply, Ublk, Vblk]
      simp_rw [hA_ent, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => by ring
    -- Next, show `M(k, i, t) := ∑ α, Ublk k α t * v (i, α)` is symmetric in `(k, i)`!
    let M : Fin r → Fin r → Fin a → K := fun k i t => ∑ α : Fin s, Ublk k α t * v.1 (i, α)
    have hfix' : ∀ (k : Fin r) (β : Fin s),
        v.1 (k, β) = ∑ i : Fin r, ∑ t' : Fin a, Vblk i β t' * M k i t' := hfix
    have hMsym : ∀ j k t, M j k t = M k j t := by
      intro j k t
      change (∑ β : Fin s, Ublk j β t * v.1 (k, β)) = M k j t
      conv_lhs => arg 2; ext β; rw [hfix' k β]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hinner : ∀ i : Fin r,
          ∑ β : Fin s, ∑ t' : Fin a, Ublk j β t * (Vblk i β t' * M k i t') =
          if i = j then M k j t else 0 := by
        intro i
        rw [Finset.sum_comm]
        have hstep : ∀ t' : Fin a,
            ∑ β : Fin s, Ublk j β t * (Vblk i β t' * M k i t') =
            ((Vblk i)ᵀ * Ublk j) t' t * M k i t' := by
          intro t'
          simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
          refine Finset.sum_congr rfl fun β _ => by ring
        simp_rw [hstep]
        rw [hVU j i]
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte, Matrix.one_apply, ite_mul, one_mul, zero_mul,
            Finset.sum_ite_eq', Finset.mem_univ]
        · simp [hij]
      change (∑ i : Fin r, ∑ β : Fin s, ∑ t' : Fin a, Ublk j β t * (Vblk i β t' * M k i t')) = M k j t
      rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_ite_eq']
      simp
    -- Since `Ψ v = 0`, `M k i t = 0` for all `k ≤ i`, hence by `hMsym` for all `k, i`!
    have hM0 : ∀ k i t, M k i t = 0 := by
      intro k i t
      rcases le_total k i with hki | hik
      · exact congrFun hv (⟨(k, i), hki⟩, t)
      · rw [hMsym k i t]
        exact congrFun hv (⟨(i, k), hik⟩, t)
    apply Subtype.ext
    ext ⟨k, β⟩
    rw [hfix k β]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun t _ => ?_
    change Vblk i β t * M k i t = 0
    rw [hM0 k i t, mul_zero]
  have hcard_upper : 2 * Fintype.card Upper = r * (r + 1) := card_upper_pairs r
  have hker_le : Module.finrank K (LinearMap.ker W.mulVecLin) ≤ Fintype.card Upper * a := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hΨ_inj
    simpa [Module.finrank_fin_fun, Fintype.card_prod, Fintype.card_fin] using h1
  have hrn : b + Module.finrank K (LinearMap.ker W.mulVecLin) = r * s := by
    have h := LinearMap.finrank_range_add_finrank_ker W.mulVecLin
    change b + Module.finrank K (LinearMap.ker W.mulVecLin) = Module.finrank K (Fin r × Fin s → K) at h
    simpa [Module.finrank_fin_fun, Fintype.card_prod, Fintype.card_fin] using h
  have h2bound : 2 * ((r - 1) * s) ≤ (r * r + r - 2) * a := by
    have hba : r * s ≤ b + Fintype.card Upper * a := by omega
    have hb_le : b + a ≤ s := by omega
    have hstep1 : 2 * (r * s) ≤ 2 * b + (2 * Fintype.card Upper) * a := by
      calc 2 * (r * s) ≤ 2 * (b + Fintype.card Upper * a) := by omega
        _ = 2 * b + (2 * Fintype.card Upper) * a := by ring
    rw [hcard_upper] at hstep1
    have hrr : 2 ≤ r * r + r := by nlinarith
    have hstep2 : 2 * b + 2 * a ≤ 2 * s := by omega
    have hrr2 : (r * (r + 1)) * a = (r * r + r - 2) * a + 2 * a := by
      zify [hrr]; ring
    have hrs2 : 2 * (r * s) = 2 * ((r - 1) * s) + 2 * s := by
      have hr1 : 1 ≤ r := by omega
      zify [hr1]; ring
    omega
  have hr_le2 : r ≤ 2 := tcB_core (by omega) ha_pos hra_le_s h2bound
  have hr_eq2 : r = 2 := by omega
  subst hr_eq2
  -- Now `2 * a ≤ s` and `2 * s ≤ 4 * a`, so `s = 2 * a` is even!
  have hs_eq : s = 2 * a := by omega
  exact ⟨rfl, ⟨a, by omega⟩⟩

/-- Characteristic-free strict lower bound: over every field `K` (including characteristic `2`),
`TC_K(r, s) ≥ max r s + 1` whenever `r ≥ 3` and `s ≥ 3`. -/
theorem twoCut_gt_max_of_ge_three {r s c : ℕ} (hr : 3 ≤ r) (hs : 3 ≤ s)
    (h : HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) c) :
    max r s + 1 ≤ c := by
  have hge := twoCut_ge_max (by omega) (by omega) h
  by_contra hlt
  have hceq : c = max r s := by omega
  subst hceq
  rcases le_total r s with hrs | hsr
  · rw [max_eq_right hrs] at h
    have ⟨hr2, _⟩ := twoCut_eq_max_forces_two_even (by omega) hrs h
    omega
  · rw [max_eq_left hsr] at h
    have h' := twoCut_swap.1 h
    have ⟨hs2, _⟩ := twoCut_eq_max_forces_two_even (by omega) hsr h'
    omega

/-- Characteristic-free `2 × s` lower bound: over every field `K`,
`TC_K(2, s) ≥ 2 * ⌈s / 2⌉` for every `s`. -/
theorem twoCut_two_lower {s c : ℕ}
    (h : HasTwoCut (1 : Matrix (Fin 2 × Fin s) (Fin 2 × Fin s) K) c) :
    2 * ((s + 1) / 2) ≤ c := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hs) with rfl | hs2
    · have := twoCut_ge_left (by omega) h; omega
    · have hge := twoCut_ge_max (by omega) (by omega) h
      have hmax : max 2 s = s := max_eq_right (by omega)
      rw [hmax] at hge
      by_cases heven : Even s
      · rcases heven with ⟨k, rfl⟩
        have : 2 * ((k + k + 1) / 2) = k + k := by omega
        omega
      · by_contra hlt
        have hcs : c = s := by omega
        subst hcs
        have ⟨_, hev⟩ := twoCut_eq_max_forces_two_even le_rfl (by omega) h
        exact heven hev

/-- Upper bound for the `(2, 2)` crossing: `TC_K(2, 2) ≤ 2` over every field `K`,
via `P = vec(I₂) vec(I₂)ᵀ` (`rank 1`) and `W = 1 - P^Γ` (`rank 1`). -/
theorem twoCut_two_two :
    HasTwoCut (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) 2 := by
  let u : Fin 2 × Fin 2 → K := fun p => if p.1 = p.2 then 1 else 0
  let v : Fin 2 × Fin 2 → K := fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0
  let A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K := Matrix.vecMulVec u u
  let W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K := Matrix.vecMulVec v v
  refine ⟨A, W, ?_, ?_⟩
  · ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [A, W, u, v, Matrix.vecMulVec_apply]
  · have hA : A.rank ≤ 1 := by
      have hfac : A = (Matrix.of fun p (_ : Fin 1) => u p) * (Matrix.of fun (_ : Fin 1) q => u q) := by
        ext p q; simp [A, Matrix.vecMulVec_apply, Matrix.mul_apply]
      rw [hfac]
      calc _ ≤ (Matrix.of fun p (_ : Fin 1) => u p).rank := Matrix.rank_mul_le_left _ _
        _ ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_width _
        _ = 1 := Fintype.card_fin 1
    have hW : W.rank ≤ 1 := by
      have hfac : W = (Matrix.of fun p (_ : Fin 1) => v p) * (Matrix.of fun (_ : Fin 1) q => v q) := by
        ext p q; simp [W, Matrix.vecMulVec_apply, Matrix.mul_apply]
      rw [hfac]
      calc _ ≤ (Matrix.of fun p (_ : Fin 1) => v p).rank := Matrix.rank_mul_le_left _ _
        _ ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_width _
        _ = 1 := Fintype.card_fin 1
    omega

/-- Restriction monotonicity: if `s₁ ≤ s₂` and `TC_K(r, s₂) ≤ c`, then `TC_K(r, s₁) ≤ c`. -/
theorem twoCut_mono_right {r s₁ s₂ c : ℕ} (hle : s₁ ≤ s₂)
    (h : HasTwoCut (1 : Matrix (Fin r × Fin s₂) (Fin r × Fin s₂) K) c) :
    HasTwoCut (1 : Matrix (Fin r × Fin s₁) (Fin r × Fin s₁) K) c := by
  rcases h with ⟨A, W, hAW, hrk⟩
  let emb : Fin r × Fin s₁ → Fin r × Fin s₂ := fun p => (p.1, Fin.castLE hle p.2)
  refine ⟨A.submatrix emb emb, W.submatrix emb emb, ?_, ?_⟩
  · ext ⟨a, b⟩ ⟨c', d⟩
    have := congrFun (congrFun hAW (a, Fin.castLE hle b)) (c', Fin.castLE hle d)
    simpa [emb, Matrix.submatrix_apply, Matrix.add_apply, ptr_apply, Matrix.one_apply,
      Prod.mk.injEq, Fin.ext_iff] using this
  · calc (A.submatrix emb emb).rank + (W.submatrix emb emb).rank
        ≤ A.rank + W.rank :=
          add_le_add (Matrix.rank_submatrix_le _ _ _) (Matrix.rank_submatrix_le _ _ _)
      _ ≤ c := hrk

/-- Direct sum of two-cut decompositions along the second side:
`TC_K(r, s₁ + s₂) ≤ TC_K(r, s₁) + TC_K(r, s₂)`. -/
theorem twoCut_add_right {r s₁ s₂ c₁ c₂ : ℕ}
    (h1 : HasTwoCut (1 : Matrix (Fin r × Fin s₁) (Fin r × Fin s₁) K) c₁)
    (h2 : HasTwoCut (1 : Matrix (Fin r × Fin s₂) (Fin r × Fin s₂) K) c₂) :
    HasTwoCut (1 : Matrix (Fin r × Fin (s₁ + s₂)) (Fin r × Fin (s₁ + s₂)) K) (c₁ + c₂) := by
  rcases h1 with ⟨A₁, W₁, hAW₁, hrk₁⟩
  rcases h2 with ⟨A₂, W₂, hAW₂, hrk₂⟩
  -- Embed `A₁, W₁` on `[0, s₁)` and `A₂, W₂` on `[s₁, s₁ + s₂)`.
  let lift1 (M : Matrix (Fin r × Fin s₁) (Fin r × Fin s₁) K) :
      Matrix (Fin r × Fin (s₁ + s₂)) (Fin r × Fin (s₁ + s₂)) K :=
    Matrix.of fun p q =>
      if hp : p.2.1 < s₁ then if hq : q.2.1 < s₁ then M (p.1, ⟨p.2.1, hp⟩) (q.1, ⟨q.2.1, hq⟩)
      else 0 else 0
  let lift2 (M : Matrix (Fin r × Fin s₂) (Fin r × Fin s₂) K) :
      Matrix (Fin r × Fin (s₁ + s₂)) (Fin r × Fin (s₁ + s₂)) K :=
    Matrix.of fun p q =>
      if hp : s₁ ≤ p.2.1 then if hq : s₁ ≤ q.2.1 then
        M (p.1, ⟨p.2.1 - s₁, by omega⟩) (q.1, ⟨q.2.1 - s₁, by omega⟩)
      else 0 else 0
  have hlift1_rk : ∀ M, (lift1 M).rank ≤ M.rank := by
    intro M
    let L : Matrix (Fin r × Fin (s₁ + s₂)) (Fin r × Fin s₁) K :=
      Matrix.of fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then 1 else 0
    let R : Matrix (Fin r × Fin s₁) (Fin r × Fin (s₁ + s₂)) K :=
      Matrix.of fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then 1 else 0
    have hfac : lift1 M = L * M * R := by
      ext ⟨a, b⟩ ⟨c', d⟩
      simp only [lift1, L, R, Matrix.of_apply, Matrix.mul_apply]
      by_cases hb : b.1 < s₁ <;> by_cases hd : d.1 < s₁
      · simp only [hb, hd, ↓reduceDIte]
        have hR : ∀ x : Fin r × Fin s₁,
            (∑ y : Fin r × Fin s₁,
              (if a = y.1 ∧ b.1 = y.2.1 then (1 : K) else 0) * M y x) *
              (if x.1 = c' ∧ x.2.1 = d.1 then 1 else 0) =
            if x = (c', ⟨d.1, hd⟩) then
              ∑ y : Fin r × Fin s₁,
                (if a = y.1 ∧ b.1 = y.2.1 then (1 : K) else 0) * M y (c', ⟨d.1, hd⟩)
            else 0 := by
          intro ⟨xc, xd⟩
          by_cases hx : (xc, xd) = (c', ⟨d.1, hd⟩)
          · rw [hx]; simp
          · have hne : ¬ (xc = c' ∧ xd.1 = d.1) := by
              rintro ⟨rfl, hxd⟩; exact hx (Prod.ext rfl (Fin.ext hxd))
            simp [hx, hne]
        simp_rw [hR, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have hL : ∀ y : Fin r × Fin s₁,
            (if a = y.1 ∧ b.1 = y.2.1 then (1 : K) else 0) * M y (c', ⟨d.1, hd⟩) =
            if y = (a, ⟨b.1, hb⟩) then M (a, ⟨b.1, hb⟩) (c', ⟨d.1, hd⟩) else 0 := by
          intro ⟨ya, yb⟩
          by_cases hy : (ya, yb) = (a, ⟨b.1, hb⟩)
          · rw [hy]; simp
          · have hne : ¬ (a = ya ∧ b.1 = yb.1) := by
              rintro ⟨rfl, hyb⟩; exact hy (Prod.ext rfl (Fin.ext hyb.symm))
            simp [hy, hne]
        simp_rw [hL, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      · simp only [hb, hd, ↓reduceDIte]
        symm; refine Finset.sum_eq_zero fun ⟨xc, xd⟩ _ => ?_
        have : ¬ (xc = c' ∧ xd.1 = d.1) := by intro ⟨_, h⟩; omega
        simp [this]
      · simp only [hb, ↓reduceDIte]
        symm; refine Finset.sum_eq_zero fun x _ => ?_
        have h0 : ∑ y : Fin r × Fin s₁, (if a = y.1 ∧ b.1 = y.2.1 then (1 : K) else 0) * M y x = 0 :=
          Finset.sum_eq_zero fun ⟨ya, yb⟩ _ => by
            have : ¬ (a = ya ∧ b.1 = yb.1) := by intro ⟨_, h⟩; omega
            simp [this]
        rw [h0, zero_mul]
      · simp only [hb, ↓reduceDIte]
        symm; refine Finset.sum_eq_zero fun x _ => ?_
        have h0 : ∑ y : Fin r × Fin s₁, (if a = y.1 ∧ b.1 = y.2.1 then (1 : K) else 0) * M y x = 0 :=
          Finset.sum_eq_zero fun ⟨ya, yb⟩ _ => by
            have : ¬ (a = ya ∧ b.1 = yb.1) := by intro ⟨_, h⟩; omega
            simp [this]
        rw [h0, zero_mul]
    rw [hfac]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hlift2_rk : ∀ M, (lift2 M).rank ≤ M.rank := by
    intro M
    let L : Matrix (Fin r × Fin (s₁ + s₂)) (Fin r × Fin s₂) K :=
      Matrix.of fun p q => if p.1 = q.1 ∧ p.2.1 = s₁ + q.2.1 then 1 else 0
    let R : Matrix (Fin r × Fin s₂) (Fin r × Fin (s₁ + s₂)) K :=
      Matrix.of fun p q => if p.1 = q.1 ∧ s₁ + p.2.1 = q.2.1 then 1 else 0
    have hfac : lift2 M = L * M * R := by
      ext ⟨a, b⟩ ⟨c', d⟩
      simp only [lift2, L, R, Matrix.of_apply, Matrix.mul_apply]
      by_cases hb : s₁ ≤ b.1 <;> by_cases hd : s₁ ≤ d.1
      · simp only [hb, hd, ↓reduceDIte]
        have hR : ∀ x : Fin r × Fin s₂,
            (∑ y : Fin r × Fin s₂,
              (if a = y.1 ∧ b.1 = s₁ + y.2.1 then (1 : K) else 0) * M y x) *
              (if x.1 = c' ∧ s₁ + x.2.1 = d.1 then 1 else 0) =
            if x = (c', ⟨d.1 - s₁, by omega⟩) then
              ∑ y : Fin r × Fin s₂,
                (if a = y.1 ∧ b.1 = s₁ + y.2.1 then (1 : K) else 0) *
                  M y (c', ⟨d.1 - s₁, by omega⟩)
            else 0 := by
          intro ⟨xc, xd⟩
          by_cases hx : (xc, xd) = (c', ⟨d.1 - s₁, by omega⟩)
          · rw [hx]; simp [show s₁ + (d.1 - s₁) = d.1 by omega]
          · have hne : ¬ (xc = c' ∧ s₁ + xd.1 = d.1) := by
              rintro ⟨rfl, hxd⟩; exact hx (Prod.ext rfl (Fin.ext (by dsimp; omega)))
            simp [hx, hne]
        simp_rw [hR, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have hL : ∀ y : Fin r × Fin s₂,
            (if a = y.1 ∧ b.1 = s₁ + y.2.1 then (1 : K) else 0) *
              M y (c', ⟨d.1 - s₁, by omega⟩) =
            if y = (a, ⟨b.1 - s₁, by omega⟩) then
              M (a, ⟨b.1 - s₁, by omega⟩) (c', ⟨d.1 - s₁, by omega⟩)
            else 0 := by
          intro ⟨ya, yb⟩
          by_cases hy : (ya, yb) = (a, ⟨b.1 - s₁, by omega⟩)
          · rw [hy]
            have hbeq : s₁ + (b.1 - s₁) = b.1 := by omega
            simp [hbeq]
          · have hne : ¬ (a = ya ∧ b.1 = s₁ + yb.1) := by
              rintro ⟨rfl, hyb⟩; exact hy (Prod.ext rfl (Fin.ext (by dsimp; omega)))
            simp [hy, hne]
        simp_rw [hL, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      · simp only [hb, hd, ↓reduceDIte]
        symm; refine Finset.sum_eq_zero fun ⟨xc, xd⟩ _ => ?_
        have : ¬ (xc = c' ∧ s₁ + xd.1 = d.1) := by intro ⟨_, h⟩; omega
        simp [this]
      · simp only [hb, ↓reduceDIte]
        symm; refine Finset.sum_eq_zero fun x _ => ?_
        have h0 : ∑ y : Fin r × Fin s₂,
            (if a = y.1 ∧ b.1 = s₁ + y.2.1 then (1 : K) else 0) * M y x = 0 :=
          Finset.sum_eq_zero fun ⟨ya, yb⟩ _ => by
            have : ¬ (a = ya ∧ b.1 = s₁ + yb.1) := by intro ⟨_, h⟩; omega
            simp [this]
        rw [h0, zero_mul]
      · simp only [hb, ↓reduceDIte]
        symm; refine Finset.sum_eq_zero fun x _ => ?_
        have h0 : ∑ y : Fin r × Fin s₂,
            (if a = y.1 ∧ b.1 = s₁ + y.2.1 then (1 : K) else 0) * M y x = 0 :=
          Finset.sum_eq_zero fun ⟨ya, yb⟩ _ => by
            have : ¬ (a = ya ∧ b.1 = s₁ + yb.1) := by intro ⟨_, h⟩; omega
            simp [this]
        rw [h0, zero_mul]
    rw [hfac]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  refine ⟨lift1 A₁ + lift2 A₂, lift1 W₁ + lift2 W₂, ?_, ?_⟩
  · ext ⟨a, b⟩ ⟨c', d⟩
    simp only [Matrix.add_apply, ptr_apply, lift1, lift2, Matrix.of_apply, Matrix.one_apply,
      Prod.mk.injEq]
    by_cases hb : b.1 < s₁ <;> by_cases hd : d.1 < s₁
    · have hb' : ¬ (s₁ ≤ b.1) := by omega
      have hd' : ¬ (s₁ ≤ d.1) := by omega
      simp only [hb, hd, hb', hd', ↓reduceDIte, add_zero]
      have h1 := congrFun (congrFun hAW₁ (a, ⟨b.1, hb⟩)) (c', ⟨d.1, hd⟩)
      simpa [Matrix.add_apply, ptr_apply, Matrix.one_apply, Prod.mk.injEq, Fin.ext_iff] using h1
    · have hb' : ¬ (s₁ ≤ b.1) := by omega
      have hd' : s₁ ≤ d.1 := by omega
      have hbd : b ≠ d := fun h => by subst h; omega
      simp [hb, hd, hb', hd', hbd]
    · have hb' : s₁ ≤ b.1 := by omega
      have hd' : ¬ (s₁ ≤ d.1) := by omega
      have hbd : b ≠ d := fun h => by subst h; omega
      simp [hb, hd, hb', hd', hbd]
    · have hb' : s₁ ≤ b.1 := by omega
      have hd' : s₁ ≤ d.1 := by omega
      simp only [hb, hd, hb', hd', ↓reduceDIte, zero_add]
      have h2 := congrFun (congrFun hAW₂ (a, ⟨b.1 - s₁, by omega⟩)) (c', ⟨d.1 - s₁, by omega⟩)
      have heq : (⟨b.1 - s₁, by omega⟩ : Fin s₂) = ⟨d.1 - s₁, by omega⟩ ↔ b = d := by
        simp only [Fin.ext_iff]; omega
      simpa [Matrix.add_apply, ptr_apply, Matrix.one_apply, Prod.mk.injEq, heq] using h2
  · calc (lift1 A₁ + lift2 A₂).rank + (lift1 W₁ + lift2 W₂).rank
        ≤ ((lift1 A₁).rank + (lift2 A₂).rank) + ((lift1 W₁).rank + (lift2 W₂).rank) :=
          add_le_add (rank_add_le' _ _) (rank_add_le' _ _)
      _ ≤ (A₁.rank + A₂.rank) + (W₁.rank + W₂.rank) :=
          add_le_add (add_le_add (hlift1_rk A₁) (hlift2_rk A₂))
                     (add_le_add (hlift1_rk W₁) (hlift2_rk W₂))
      _ ≤ c₁ + c₂ := by omega

/-- Characteristic-free `2 × s` upper bound: over every field `K`,
`TC_K(2, s) ≤ 2 * ⌈s / 2⌉` for every `s`. -/
theorem twoCut_two_upper (s : ℕ) :
    HasTwoCut (1 : Matrix (Fin 2 × Fin s) (Fin 2 × Fin s) K) (2 * ((s + 1) / 2)) := by
  have heven : ∀ k : ℕ,
      HasTwoCut (1 : Matrix (Fin 2 × Fin (2 * k)) (Fin 2 × Fin (2 * k)) K) (2 * k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, 0, ?_, by simp⟩
      ext ⟨_, b⟩; exact Fin.elim0 b
    | succ k ih =>
      have h := twoCut_add_right ih (twoCut_two_two (K := K))
      simpa [Nat.mul_succ] using h
  have hle : s ≤ 2 * ((s + 1) / 2) := by omega
  exact twoCut_mono_right hle (heven ((s + 1) / 2))

/-- Characteristic-free `2 × s` exact characterisation: over every field `K`
(including characteristic `2`), `TC_K(2, s) = 2 * ⌈s / 2⌉`. -/
theorem twoCut_two_iff (s c : ℕ) :
    HasTwoCut (1 : Matrix (Fin 2 × Fin s) (Fin 2 × Fin s) K) c ↔ 2 * ((s + 1) / 2) ≤ c := by
  constructor
  · exact twoCut_two_lower
  · intro hc
    obtain ⟨A, W, hAW, hrk⟩ := twoCut_two_upper (K := K) s
    exact ⟨A, W, hAW, le_trans hrk hc⟩

/-- The transpose point (valid over every field `K`, including characteristic `2`):
`TC_K(r, s) ≤ 1 + r * s - min r s * (min r s + 1) / 2`.
In particular `TC_K(3, 3) ≤ 4`, `TC_K(3, 4) ≤ 7`, and `TC_K(4, 4) ≤ 7`. -/
theorem transpose_twoCut (r s : ℕ) :
    HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
      (1 + (r * s - min r s * (min r s + 1) / 2)) := by
  classical
  set m := min r s
  -- Rank-1 matrix `W = u uᵀ` where `u(a, b) = 1` iff `a.1 = b.1 ∧ a.1 < m`.
  let u : Fin r × Fin s → K := fun p => if p.1.1 = p.2.1 ∧ p.1.1 < m then 1 else 0
  let W : Matrix (Fin r × Fin s) (Fin r × Fin s) K := Matrix.vecMulVec u u
  let A : Matrix (Fin r × Fin s) (Fin r × Fin s) K := 1 - ptr W
  refine ⟨A, W, by simp [A], ?_⟩
  have hW_rk : W.rank ≤ 1 := by
    have hfac : W = (Matrix.of fun p (_ : Fin 1) => u p) * (Matrix.of fun (_ : Fin 1) q => u q) := by
      ext p q; simp [W, Matrix.vecMulVec_apply, Matrix.mul_apply]
    rw [hfac]
    calc _ ≤ (Matrix.of fun p (_ : Fin 1) => u p).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_width _
      _ = 1 := Fintype.card_fin 1
  -- Show `dim ker(A) ≥ m * (m + 1) / 2`!
  -- Notice `(ptr W) (a, b) (c, d) = 1` iff `a.1 = d.1 ∧ b.1 = c.1 ∧ a.1 < m ∧ b.1 < m`.
  -- So `ptr W` fixes `(i, i)` (`i < m`) and swaps `(i, j) ↔ (j, i)` (`i < j < m`).
  -- Thus for every `i ≤ j < m`, `z_{i,j} = e_{(i,i)}` (if `i = j`) or `e_{(i,j)} + e_{(j,i)}` (if `i < j`)
  -- lies in `ker(A) = Fix(ptr W)`, and these `m*(m+1)/2` vectors are linearly independent!
  let Upper := { p : Fin m × Fin m // p.1 ≤ p.2 }
  let inj : Upper → (Fin r × Fin s → K) := fun ⟨⟨i, j⟩, _⟩ p =>
    if i = j then (if p.1.1 = i.1 ∧ p.2.1 = i.1 then 1 else 0)
    else (if (p.1.1 = i.1 ∧ p.2.1 = j.1) ∨ (p.1.1 = j.1 ∧ p.2.1 = i.1) then 1 else 0)
  have hmem : ∀ q : Upper, inj q ∈ LinearMap.ker A.mulVecLin := by
    rintro ⟨⟨i, j⟩, hij⟩
    rw [LinearMap.mem_ker]
    ext ⟨a, b⟩
    change (A.mulVec (inj ⟨(i, j), hij⟩)) (a, b) = 0
    simp only [A, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero]
    -- Compute `(ptr W).mulVec (inj q) (a, b)`.
    have hmul : (ptr W).mulVec (inj ⟨(i, j), hij⟩) (a, b) =
        if ha : a.1 < m then if hb : b.1 < m then
          inj ⟨(i, j), hij⟩ (⟨b.1, by omega⟩, ⟨a.1, by omega⟩)
        else 0 else 0 := by
      simp only [Matrix.mulVec, dotProduct, ptr_apply, W, Matrix.vecMulVec_apply, u]
      by_cases ha : a.1 < m <;> by_cases hb : b.1 < m
      · simp only [ha, hb, ↓reduceDIte, and_true]
        have hterm : ∀ x : Fin r × Fin s,
            (if a.1 = x.2.1 then (1 : K) else 0) *
              (if x.1.1 = b.1 ∧ x.1.1 < m then (1 : K) else 0) *
              inj ⟨(i, j), hij⟩ x =
            if x = (⟨b.1, by omega⟩, ⟨a.1, by omega⟩) then
              inj ⟨(i, j), hij⟩ (⟨b.1, by omega⟩, ⟨a.1, by omega⟩)
            else 0 := by
          rintro ⟨xc, xd⟩
          by_cases hx : (xc, xd) = (⟨b.1, by omega⟩, ⟨a.1, by omega⟩)
          · rw [hx]; simp [hb]
          · have hne : ¬ (a.1 = xd.1 ∧ xc.1 = b.1) := by
              rintro ⟨h1, h2⟩
              exact hx (Prod.ext (Fin.ext h2) (Fin.ext h1.symm))
            simp only [hx, ↓reduceIte]
            by_cases h1 : a.1 = xd.1 <;> by_cases h2 : xc.1 = b.1
            · exact (hne ⟨h1, h2⟩).elim
            · simp [h1, h2]
            · simp [h1, h2]
            · simp [h1, h2]
        rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_ite_eq']
        simp
      · simp only [ha, hb, ↓reduceDIte]
        refine Finset.sum_eq_zero fun ⟨xc, xd⟩ _ => ?_
        have : ¬ (xc.1 = b.1 ∧ xc.1 < m) := by intro ⟨h1, h2⟩; omega
        simp [this]
      · simp only [ha, ↓reduceDIte]
        refine Finset.sum_eq_zero fun ⟨xc, xd⟩ _ => by simp
      · simp only [ha, ↓reduceDIte]
        refine Finset.sum_eq_zero fun ⟨xc, xd⟩ _ => by simp
    rw [hmul]
    by_cases ha : a.1 < m <;> by_cases hb : b.1 < m
    · simp only [ha, hb, ↓reduceDIte, inj]
      by_cases heq : i = j
      · subst heq; simp [and_comm]
      · simp [heq, or_comm, and_comm]
    · simp only [ha, hb, ↓reduceDIte, inj]
      by_cases heq : i = j
      · subst heq; have : ¬ (a.1 = i.1 ∧ b.1 = i.1) := by intro ⟨_, h⟩; omega
        simp [this]
      · have : ¬ ((a.1 = i.1 ∧ b.1 = j.1) ∨ (a.1 = j.1 ∧ b.1 = i.1)) := by
          rintro (⟨_, h⟩ | ⟨_, h⟩) <;> omega
        simp [heq, this]
    · simp only [ha, ↓reduceDIte, inj]
      by_cases heq : i = j
      · subst heq; have : ¬ (a.1 = i.1 ∧ b.1 = i.1) := by intro ⟨h, _⟩; omega
        simp [this]
      · have : ¬ ((a.1 = i.1 ∧ b.1 = j.1) ∨ (a.1 = j.1 ∧ b.1 = i.1)) := by
          rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega
        simp [heq, this]
    · simp only [ha, ↓reduceDIte, inj]
      by_cases heq : i = j
      · subst heq; have : ¬ (a.1 = i.1 ∧ b.1 = i.1) := by intro ⟨h, _⟩; omega
        simp [this]
      · have : ¬ ((a.1 = i.1 ∧ b.1 = j.1) ∨ (a.1 = j.1 ∧ b.1 = i.1)) := by
          rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega
        simp [heq, this]
  -- Linear independence of `inj` (each `q = (i, j)` with `i ≤ j` is the ONLY vector supported at `(i, j)`!).
  have hind : LinearIndependent K (fun q : Upper => (⟨inj q, hmem q⟩ : LinearMap.ker A.mulVecLin)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc ⟨⟨i₀, j₀⟩, hij₀⟩
    have hval := congrFun (congrArg Subtype.val hc) (⟨i₀.1, by omega⟩, ⟨j₀.1, by omega⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] at hval
    have hterm : ∀ q : Upper,
        c q * inj q (⟨i₀.1, by omega⟩, ⟨j₀.1, by omega⟩) =
        if q = ⟨(i₀, j₀), hij₀⟩ then c ⟨(i₀, j₀), hij₀⟩ else 0 := by
      rintro ⟨⟨i, j⟩, hij⟩
      by_cases hq : (⟨(i, j), hij⟩ : Upper) = ⟨(i₀, j₀), hij₀⟩
      · rw [hq]; dsimp only [inj]; by_cases heq : i₀ = j₀ <;> simp [heq]
      · have hne : ¬ (i = i₀ ∧ j = j₀) := fun ⟨h1, h2⟩ => hq (by subst h1 h2; rfl)
        have hne_swap : ¬ (i₀ = j ∧ j₀ = i) := by
          rintro ⟨h1, h2⟩
          have hji : j ≤ i := by
            have : i₀ ≤ j₀ := hij₀
            rwa [h1, h2] at this
          have heq_ij : i = j := le_antisymm hij hji
          exact hne ⟨heq_ij.trans h1.symm, heq_ij.symm.trans h2.symm⟩
        have h0 : inj ⟨(i, j), hij⟩ (⟨i₀.1, by omega⟩, ⟨j₀.1, by omega⟩) = 0 := by
          dsimp only [inj]
          by_cases heq : i = j
          · subst heq
            have : ¬ (i₀.1 = i.1 ∧ j₀.1 = i.1) := by
              rintro ⟨h1, h2⟩; exact hne ⟨(Fin.ext h1).symm, (Fin.ext h2).symm⟩
            simp [this]
          · have : ¬ ((i₀.1 = i.1 ∧ j₀.1 = j.1) ∨ (i₀.1 = j.1 ∧ j₀.1 = i.1)) := by
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact hne ⟨(Fin.ext h1).symm, (Fin.ext h2).symm⟩
              · exact hne_swap ⟨Fin.ext h1, Fin.ext h2⟩
            simp [heq, this]
        simp [hq, h0]
    rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_ite_eq'] at hval
    simpa using hval
  have hker_ge : Fintype.card Upper ≤ Module.finrank K (LinearMap.ker A.mulVecLin) :=
    hind.fintype_card_le_finrank
  have hcard_upper : 2 * Fintype.card Upper = m * (m + 1) := card_upper_pairs m
  have hrn : A.rank + Module.finrank K (LinearMap.ker A.mulVecLin) = r * s := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    change A.rank + Module.finrank K (LinearMap.ker A.mulVecLin) =
      Module.finrank K (Fin r × Fin s → K) at h
    simpa [Module.finrank_fin_fun, Fintype.card_prod, Fintype.card_fin] using h
  omega

/-- Exact value `TC_K(3, 3) = 4` over every field `K` (including characteristic `2`). -/
theorem twoCut_three_three_iff (c : ℕ) :
    HasTwoCut (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) K) c ↔ 4 ≤ c := by
  constructor
  · intro h; exact twoCut_gt_max_of_ge_three le_rfl le_rfl h
  · intro hc
    obtain ⟨A, W, hAW, hrk⟩ := transpose_twoCut (K := K) 3 3
    have h4 : 1 + (3 * 3 - min 3 3 * (min 3 3 + 1) / 2) = 4 := by norm_num
    rw [h4] at hrk
    exact ⟨A, W, hAW, le_trans hrk hc⟩

end PastaMath.TwoCutSoS
