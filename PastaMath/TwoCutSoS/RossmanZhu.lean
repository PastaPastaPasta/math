-- SPDX-License-Identifier: Apache-2.0
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import PastaMath.TwoCutSoS.Dictionary

/-!
# Counterexamples to Rossman–Zhu Lemma 3.13 and Proposition 3.16

In Rossman and Zhu, "Multiquadratic Sum-of-Squares Lower Bounds Imply VNC¹ ≠ VNP",
Section 3.2:
* Lemma 3.13 claims `SoS(Q_M) ≤ PT-rank(M)` over any algebraically closed field of `char ≠ 2`.
* Proposition 3.16 claims `SoS(Q_M) - 1 ≤ PT-rank(M) ≤ 2^{d-1} SoS(Q_M)` for every `n^d × n^d`
  matrix `M` over an algebraically closed or finite field of `char ≠ 2`.

We exhibit explicit `d = 2` counterexamples over every field `K` of characteristic ≠ 2:
1. `M₁ = E_{(0,0),(0,1)}` on `Fin 2 × Fin 2` (`Q_{M₁} = x₀² y₀ y₁`):
   `PT-rank(M₁) = 1` (`IsPTBasic M₁`), yet `¬ HasSoSFormula M₁ 1` (and `SoS = 2` when `√(-1) ∈ K`).
   This refutes Lemma 3.13.
2. `M₂ = E_{(0,0),(0,1)} + E_{(1,2),(1,3)}` on `Fin 4 × Fin 4` (`Q_{M₂} = x₀² y₀ y₁ + x₁² y₂ y₃`):
   `PT-rank(M₂) ≤ 2`, yet `¬ HasSoSFormula M₂ 3` (and `SoS = 4` when `√(-1) ∈ K`).
   This refutes the left-hand inequality of Proposition 3.16 even over algebraically closed fields,
   and shows that the repaired bound `SoS(Q_M) ≤ 2 · PT-rank(M)` (`sos_of_ptRank`) is sharp at
   `c = 1` and `c = 2`.
3. `M₃ = E_{(0,0),(0,1)} - E_{(0,1),(0,0)}` on `Fin 2 × Fin 2` (`Q_{M₃} = 0`):
   `HasSoSFormula M₃ 0`, yet `¬ HasPTRank M₃ 0` (`M₃ ≠ 0`).
   This refutes the right-hand inequality of Proposition 3.16 as stated (which omits Lemma 3.15's
   "fully symmetric" hypothesis).
-/

namespace PastaMath.TwoCutSoS

open Matrix Finset

variable {K : Type*} [Field K]

/-- Single-entry matrix `E_{p, q}` on `Fin r × Fin s`. -/
def elemM {r s : ℕ} (p q : Fin r × Fin s) : Matrix (Fin r × Fin s) (Fin r × Fin s) K :=
  Matrix.of fun i j => if i = p ∧ j = q then 1 else 0

lemma elemM_rank_one {r s : ℕ} (p q : Fin r × Fin s) :
    (elemM (K := K) p q).rank = 1 := by
  have hfac : elemM (K := K) p q =
      Matrix.vecMulVec (fun i => if i = p then (1 : K) else 0)
                       (fun j => if j = q then (1 : K) else 0) := by
    ext i j; simp [elemM, Matrix.vecMulVec_apply]; by_cases h1 : i = p <;> by_cases h2 : j = q <;> simp [h1, h2]
  have hle : (elemM (K := K) p q).rank ≤ 1 := by
    rw [hfac]
    have hm : Matrix.vecMulVec (fun i => if i = p then (1 : K) else 0)
        (fun j => if j = q then (1 : K) else 0) =
        (Matrix.of fun i (_ : Fin 1) => if i = p then (1 : K) else 0) *
        (Matrix.of fun (_ : Fin 1) j => if j = q then (1 : K) else 0) := by
      ext i j; simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
    rw [hm]
    calc _ ≤ (Matrix.of fun i (_ : Fin 1) => if i = p then (1 : K) else 0).rank :=
          Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_width _
      _ = 1 := Fintype.card_fin 1
  have hne : elemM (K := K) p q ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 p) q
    simp [elemM] at this
  have hpos : 0 < (elemM (K := K) p q).rank := by
    by_contra h0
    have hr0 : (elemM (K := K) p q).rank = 0 := Nat.eq_zero_of_not_pos h0
    apply hne
    apply Matrix.toLin'.injective
    rw [map_zero]
    have hbot : LinearMap.range (elemM (K := K) p q).mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.1 hr0
    apply LinearMap.ext
    intro x
    have hx : (elemM (K := K) p q).mulVecLin x ∈ (⊥ : Submodule K (Fin r × Fin s → K)) := by
      rw [← hbot]; exact ⟨x, rfl⟩
    rw [Submodule.mem_bot] at hx
    exact hx
  omega

lemma elemM_isPTBasic {r s : ℕ} (p q : Fin r × Fin s) :
    IsPTBasic (elemM (K := K) p q) :=
  Or.inl (elemM_rank_one p q)

/-- Counterexample matrix for Rossman–Zhu Lemma 3.13: `M₁ = E_{(0,0),(0,1)}` on `Fin 2 × Fin 2`,
giving `Q_{M₁}(x, y) = x₀² y₀ y₁`. -/
def rzM1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K :=
  elemM (0, 0) (0, 1)

theorem rzM1_isPTBasic : IsPTBasic (rzM1 (K := K)) :=
  elemM_isPTBasic (0, 0) (0, 1)

theorem rzM1_hasPTRank_one : HasPTRank (rzM1 (K := K)) 1 :=
  ⟨1, fun _ => rzM1, le_rfl, fun _ => rzM1_isPTBasic, by simp⟩

/-- `Q_{M₁} = x₀² y₀ y₁` is not the square of a single bilinear form over any field of `char ≠ 2`. -/
theorem rzM1_not_sos_one (h2 : (2 : K) ≠ 0) : ¬ HasSoSFormula (rzM1 (K := K)) 1 := by
  rintro ⟨L, hL⟩
  have hL' := sym4_eq_of_sameBiquad hL
  have h00 := congrFun (congrFun hL' (0, 0)) (0, 0)
  have h01 := congrFun (congrFun hL' (0, 0)) (0, 1)
  simp [sym4, rzM1, elemM, Matrix.mul_apply] at h00 h01
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hsq : L 0 (0, 0) * L 0 (0, 0) = 0 := by
    apply mul_left_cancel₀ h4
    linear_combination h00
  have hz : L 0 (0, 0) = 0 := mul_self_eq_zero.1 hsq
  have h01' : (4 : K) * (L 0 (0, 0) * L 0 (0, 1)) = 2 := by
    linear_combination h01
  rw [hz, zero_mul, mul_zero] at h01'
  exact h2 h01'.symm

/-- Refutation of Rossman–Zhu Lemma 3.13 over every field `K` of characteristic ≠ 2. -/
theorem rz_lemma313_counterexample (h2 : (2 : K) ≠ 0) :
    HasPTRank (rzM1 (K := K)) 1 ∧ ¬ HasSoSFormula (rzM1 (K := K)) 1 :=
  ⟨rzM1_hasPTRank_one, rzM1_not_sos_one h2⟩

/-- When `√(-1) ∈ K`, `SoS(Q_{M₁}) = 2`, matching `2 · PT-rank(M₁)`. -/
theorem rzM1_hasSoS_two (h2 : (2 : K) ≠ 0) {I : K} (hI : I ^ 2 = -1) :
    HasSoSFormula (rzM1 (K := K)) 2 :=
  sos_of_ptRank h2 hI rzM1 rzM1_hasPTRank_one

/-- Counterexample matrix for Rossman–Zhu Proposition 3.16 (left inequality):
`M₂ = E_{(0,0),(0,1)} + E_{(1,2),(1,3)}` on `Fin 4 × Fin 4`,
giving `Q_{M₂}(x, y) = x₀² y₀ y₁ + x₁² y₂ y₃`. -/
def rzM2 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) K :=
  elemM (0, 0) (0, 1) + elemM (1, 2) (1, 3)

theorem rzM2_hasPTRank_two : HasPTRank (rzM2 (K := K)) 2 := by
  refine ⟨2, fun i => if i = 0 then elemM (0, 0) (0, 1) else elemM (1, 2) (1, 3), le_rfl, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact elemM_isPTBasic (0, 0) (0, 1)
    · exact elemM_isPTBasic (1, 2) (1, 3)
  · simp [rzM2, Fin.sum_univ_two]

/-- Helper: in `K³`, there cannot exist four vectors `u₁, u₂, v₁, v₂` forming two mutually
orthogonal hyperbolic planes (`u₁·u₁ = u₂·u₂ = v₁·v₁ = v₂·v₂ = 0`, `u₁·u₂ ≠ 0`, `v₁·v₂ ≠ 0`,
and `uᵢ·vⱼ = 0`). -/
private lemma no_two_orth_hyperbolic_in_fin3
    (u₁ u₂ v₁ v₂ : Fin 3 → K)
    (hu₁ : dotProduct u₁ u₁ = 0) (hu₂ : dotProduct u₂ u₂ = 0) (hu12 : dotProduct u₁ u₂ ≠ 0)
    (hv₁ : dotProduct v₁ v₁ = 0) (hv₂ : dotProduct v₂ v₂ = 0) (hv12 : dotProduct v₁ v₂ ≠ 0)
    (h11 : dotProduct u₁ v₁ = 0) (h12 : dotProduct u₁ v₂ = 0)
    (h21 : dotProduct u₂ v₁ = 0) (h22 : dotProduct u₂ v₂ = 0) : False := by
  -- Show the four vectors `u₁, u₂, v₁, v₂` are linearly independent in `Fin 3 → K`,
  -- contradicting `finrank K (Fin 3 → K) = 3`.
  let vecs : Fin 4 → (Fin 3 → K) := fun i =>
    match i with
    | ⟨0, _⟩ => u₁
    | ⟨1, _⟩ => u₂
    | ⟨2, _⟩ => v₁
    | ⟨3, _⟩ => v₂
  have hind : LinearIndependent K vecs := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hdot : ∀ w : Fin 3 → K,
        c 0 * dotProduct w u₁ + c 1 * dotProduct w u₂ +
        c 2 * dotProduct w v₁ + c 3 * dotProduct w v₂ = 0 := by
      intro w
      have h0 : dotProduct w (∑ i : Fin 4, c i • vecs i) = 0 := by rw [hc, dotProduct_zero]
      simp only [Fin.sum_univ_four, vecs, dotProduct_add, dotProduct_smul, smul_eq_mul] at h0
      linear_combination h0
    have hdot_sym : ∀ a b : Fin 3 → K, dotProduct a b = dotProduct b a := dotProduct_comm
    have hc1 : c 1 * dotProduct u₁ u₂ = 0 := by
      have := hdot u₁
      rw [hu₁, h11, h12] at this
      linear_combination this
    have hc0 : c 0 * dotProduct u₁ u₂ = 0 := by
      have := hdot u₂
      rw [hdot_sym u₂ u₁, hu₂, h21, h22] at this
      linear_combination this
    have hc3 : c 3 * dotProduct v₁ v₂ = 0 := by
      have := hdot v₁
      rw [hdot_sym v₁ u₁, hdot_sym v₁ u₂, h11, h21, hv₁] at this
      linear_combination this
    have hc2 : c 2 * dotProduct v₁ v₂ = 0 := by
      have := hdot v₂
      rw [hdot_sym v₂ u₁, hdot_sym v₂ u₂, hdot_sym v₂ v₁, h12, h22, hv₂] at this
      linear_combination this
    intro i
    fin_cases i
    · exact (mul_eq_zero.1 hc0).resolve_right hu12
    · exact (mul_eq_zero.1 hc1).resolve_right hu12
    · exact (mul_eq_zero.1 hc2).resolve_right hv12
    · exact (mul_eq_zero.1 hc3).resolve_right hv12
  have hcard := hind.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_fin_fun] at hcard
  omega

/-- In `K³`, an isotropic vector `w` orthogonal to a hyperbolic plane `{u₁, u₂}` must vanish:
otherwise `{u₁, u₂, w}` is a basis of `K³`, forcing `w` orthogonal to all of `K³`, contradicting
nondegeneracy of the standard dot product. -/
private lemma zero_of_iso_orth_hyperbolic
    (u₁ u₂ w : Fin 3 → K)
    (hu₁ : dotProduct u₁ u₁ = 0) (hu₂ : dotProduct u₂ u₂ = 0) (hu12 : dotProduct u₁ u₂ ≠ 0)
    (hw : dotProduct w w = 0) (hw1 : dotProduct u₁ w = 0) (hw2 : dotProduct u₂ w = 0) :
    w = 0 := by
  by_contra hne
  let vecs : Fin 3 → (Fin 3 → K) := fun i =>
    match i with
    | ⟨0, _⟩ => u₁
    | ⟨1, _⟩ => u₂
    | ⟨2, _⟩ => w
  have hind : LinearIndependent K vecs := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hdot : ∀ z : Fin 3 → K,
        c 0 * dotProduct z u₁ + c 1 * dotProduct z u₂ + c 2 * dotProduct z w = 0 := by
      intro z
      have h0 : dotProduct z (∑ i : Fin 3, c i • vecs i) = 0 := by rw [hc, dotProduct_zero]
      simp only [Fin.sum_univ_three, vecs, dotProduct_add, dotProduct_smul, smul_eq_mul] at h0
      linear_combination h0
    have hc1 : c 1 = 0 := by
      have := hdot u₁
      rw [hu₁, hw1] at this
      exact (mul_eq_zero.1 (by linear_combination this : c 1 * dotProduct u₁ u₂ = 0)).resolve_right hu12
    have hc0 : c 0 = 0 := by
      have := hdot u₂
      rw [dotProduct_comm u₂ u₁, hu₂, hw2] at this
      exact (mul_eq_zero.1 (by linear_combination this : c 0 * dotProduct u₁ u₂ = 0)).resolve_right hu12
    have hc2w : c 2 • w = 0 := by
      have hsum : c 0 • u₁ + c 1 • u₂ + c 2 • w = 0 := by
        simpa [Fin.sum_univ_three, vecs] using hc
      rw [hc0, hc1, zero_smul, zero_smul, zero_add, zero_add] at hsum
      exact hsum
    have hc2 : c 2 = 0 := (smul_eq_zero.1 hc2w).resolve_right hne
    intro i; fin_cases i <;> assumption
  let b := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
  apply hne
  ext j
  have hrepr := b.sum_repr (Pi.single j (1 : K))
  have hdotw : dotProduct (Pi.single j (1 : K)) w = 0 := by
    rw [← hrepr]
    simp only [Fin.sum_univ_three, b, coe_basisOfLinearIndependentOfCardEqFinrank, vecs,
      add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hw1, hw2, hw]
    ring
  simpa [dotProduct, Pi.single_apply] using hdotw

/-- `Q_{M₂} = x₀² y₀ y₁ + x₁² y₂ y₃` cannot be written as a sum of 3 squares of bilinear forms
over any field of characteristic ≠ 2. -/
theorem rzM2_not_sos_three (h2 : (2 : K) ≠ 0) : ¬ HasSoSFormula (rzM2 (K := K)) 3 := by
  rintro ⟨L, hL⟩
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  -- Extract column vectors `col (a, b) : Fin 3 → K` of `L`.
  let col : Fin 4 × Fin 4 → (Fin 3 → K) := fun p l => L l p
  have hdot_sym : ∀ p q : Fin 4 × Fin 4,
      (Lᵀ * L) p q = dotProduct (col p) (col q) := by
    intro p q; rfl
  -- Helper to read off `sym4 (Lᵀ * L) (a, b) (c, d) = sym4 rzM2 (a, b) (c, d)`.
  have hentry : ∀ (a c : Fin 4) (b d : Fin 4),
      2 * (dotProduct (col (a, b)) (col (c, d)) + dotProduct (col (a, d)) (col (c, b))) =
        sym4 (rzM2 (K := K)) (a, b) (c, d) := by
    intro a c b d
    have h := congrFun (congrFun (sym4_eq_of_sameBiquad hL) (a, b)) (c, d)
    unfold sym4 at h ⊢
    simp only [Matrix.add_apply, Matrix.transpose_apply, ptr_apply, hdot_sym] at h ⊢
    rw [dotProduct_comm (col (c, d)) (col (a, b)),
        dotProduct_comm (col (c, b)) (col (a, d))] at h
    linear_combination h
  -- Diagonal entries `(a, b) = (c, d)` give `dotProduct (col (a, b)) (col (a, b)) = 0`.
  have hiso : ∀ (a b : Fin 4), dotProduct (col (a, b)) (col (a, b)) = 0 := by
    intro a b
    have h := hentry a a b b
    have hrhs : sym4 (rzM2 (K := K)) (a, b) (a, b) = 0 := by
      unfold sym4 rzM2 elemM
      fin_cases a <;> fin_cases b <;> simp
    rw [hrhs] at h
    apply mul_left_cancel₀ h4
    linear_combination h
  -- Same-x entries `(a, b), (a, d)` give `4 * dot(col(a,b), col(a,d)) = sym4 rzM2 (a,b) (a,d)`.
  have hsameX : ∀ (a b d : Fin 4),
      4 * dotProduct (col (a, b)) (col (a, d)) = sym4 (rzM2 (K := K)) (a, b) (a, d) := by
    intro a b d
    have h := hentry a a b d
    rw [dotProduct_comm (col (a, d)) (col (a, b))] at h
    linear_combination h
  -- Hyperbolic plane 1: `u₁ = col (0, 0)`, `u₂ = col (0, 1)`.
  have hu12 : dotProduct (col (0, 0)) (col (0, 1)) ≠ 0 := by
    have h := hsameX 0 0 1
    have hrhs : sym4 (rzM2 (K := K)) (0, 0) (0, 1) = 2 := by
      unfold sym4 rzM2 elemM; simp; ring
    rw [hrhs] at h
    intro hz
    rw [hz, mul_zero] at h
    exact h2 h.symm
  -- Hyperbolic plane 2: `v₁ = col (1, 2)`, `v₂ = col (1, 3)`.
  have hv12 : dotProduct (col (1, 2)) (col (1, 3)) ≠ 0 := by
    have h := hsameX 1 2 3
    have hrhs : sym4 (rzM2 (K := K)) (1, 2) (1, 3) = 2 := by
      unfold sym4 rzM2 elemM; simp; ring
    rw [hrhs] at h
    intro hz
    rw [hz, mul_zero] at h
    exact h2 h.symm
  -- Show `col (0, 2) = 0` and `col (0, 3) = 0` (orthogonal to `{u₁, u₂}` and isotropic).
  have hcol02 : col (0, 2) = 0 := by
    apply zero_of_iso_orth_hyperbolic (col (0, 0)) (col (0, 1)) (col (0, 2))
      (hiso 0 0) (hiso 0 1) hu12 (hiso 0 2)
    · have h := hsameX 0 0 2
      have hrhs : sym4 (rzM2 (K := K)) (0, 0) (0, 2) = 0 := by unfold sym4 rzM2 elemM; simp
      rw [hrhs] at h; exact (mul_eq_zero.1 h).resolve_left h4
    · have h := hsameX 0 1 2
      have hrhs : sym4 (rzM2 (K := K)) (0, 1) (0, 2) = 0 := by unfold sym4 rzM2 elemM; simp
      rw [hrhs] at h; exact (mul_eq_zero.1 h).resolve_left h4
  have hcol03 : col (0, 3) = 0 := by
    apply zero_of_iso_orth_hyperbolic (col (0, 0)) (col (0, 1)) (col (0, 3))
      (hiso 0 0) (hiso 0 1) hu12 (hiso 0 3)
    · have h := hsameX 0 0 3
      have hrhs : sym4 (rzM2 (K := K)) (0, 0) (0, 3) = 0 := by unfold sym4 rzM2 elemM; simp
      rw [hrhs] at h; exact (mul_eq_zero.1 h).resolve_left h4
    · have h := hsameX 0 1 3
      have hrhs : sym4 (rzM2 (K := K)) (0, 1) (0, 3) = 0 := by unfold sym4 rzM2 elemM; simp
      rw [hrhs] at h; exact (mul_eq_zero.1 h).resolve_left h4
  -- Show `col (1, 0) = 0` and `col (1, 1) = 0` (orthogonal to `{v₁, v₂}` and isotropic).
  have hcol10 : col (1, 0) = 0 := by
    apply zero_of_iso_orth_hyperbolic (col (1, 2)) (col (1, 3)) (col (1, 0))
      (hiso 1 2) (hiso 1 3) hv12 (hiso 1 0)
    · have h := hsameX 1 2 0
      have hrhs : sym4 (rzM2 (K := K)) (1, 2) (1, 0) = 0 := by unfold sym4 rzM2 elemM; simp
      rw [hrhs] at h; exact (mul_eq_zero.1 h).resolve_left h4
    · have h := hsameX 1 3 0
      have hrhs : sym4 (rzM2 (K := K)) (1, 3) (1, 0) = 0 := by unfold sym4 rzM2 elemM; simp
      rw [hrhs] at h; exact (mul_eq_zero.1 h).resolve_left h4
  have hcol11 : col (1, 1) = 0 := by
    apply zero_of_iso_orth_hyperbolic (col (1, 2)) (col (1, 3)) (col (1, 1))
      (hiso 1 2) (hiso 1 3) hv12 (hiso 1 1)
    · have h := hsameX 1 2 1
      have hrhs : sym4 (rzM2 (K := K)) (1, 2) (1, 1) = 0 := by unfold sym4 rzM2 elemM; simp
      rw [hrhs] at h; exact (mul_eq_zero.1 h).resolve_left h4
    · have h := hsameX 1 3 1
      have hrhs : sym4 (rzM2 (K := K)) (1, 3) (1, 1) = 0 := by unfold sym4 rzM2 elemM; simp
      rw [hrhs] at h; exact (mul_eq_zero.1 h).resolve_left h4
  -- Cross-terms `x₀ x₁ y_b y_d` for `b ∈ {0, 1}, d ∈ {2, 3}` now force `uᵢ ⊥ vⱼ`!
  have horth : ∀ (b d : Fin 4), col (0, d) = 0 → col (1, b) = 0 →
      sym4 (rzM2 (K := K)) (0, b) (1, d) = 0 →
      dotProduct (col (0, b)) (col (1, d)) = 0 := by
    intro b d h0d h1b hrhs
    have h := hentry 0 1 b d
    rw [h0d, h1b, zero_dotProduct, add_zero, hrhs] at h
    exact (mul_eq_zero.1 h).resolve_left h2
  have h11 : dotProduct (col (0, 0)) (col (1, 2)) = 0 :=
    horth 0 2 hcol02 hcol10 (by unfold sym4 rzM2 elemM; simp)
  have h12 : dotProduct (col (0, 0)) (col (1, 3)) = 0 :=
    horth 0 3 hcol03 hcol10 (by unfold sym4 rzM2 elemM; simp)
  have h21 : dotProduct (col (0, 1)) (col (1, 2)) = 0 :=
    horth 1 2 hcol02 hcol11 (by unfold sym4 rzM2 elemM; simp)
  have h22 : dotProduct (col (0, 1)) (col (1, 3)) = 0 :=
    horth 1 3 hcol03 hcol11 (by unfold sym4 rzM2 elemM; simp)
  exact no_two_orth_hyperbolic_in_fin3
    (col (0, 0)) (col (0, 1)) (col (1, 2)) (col (1, 3))
    (hiso 0 0) (hiso 0 1) hu12 (hiso 1 2) (hiso 1 3) hv12 h11 h12 h21 h22

/-- Refutation of the left-hand inequality of Rossman–Zhu Proposition 3.16
(`SoS(Q_M) - 1 ≤ PT-rank(M)`) over every field `K` of characteristic ≠ 2. -/
theorem rz_prop316_left_counterexample (h2 : (2 : K) ≠ 0) :
    HasPTRank (rzM2 (K := K)) 2 ∧ ¬ HasSoSFormula (rzM2 (K := K)) 3 :=
  ⟨rzM2_hasPTRank_two, rzM2_not_sos_three h2⟩

/-- When `√(-1) ∈ K`, `SoS(Q_{M₂}) = 4`, matching `2 · PT-rank(M₂)`. -/
theorem rzM2_hasSoS_four (h2 : (2 : K) ≠ 0) {I : K} (hI : I ^ 2 = -1) :
    HasSoSFormula (rzM2 (K := K)) 4 :=
  sos_of_ptRank h2 hI rzM2 rzM2_hasPTRank_two

/-- Counterexample matrix for the right-hand inequality of Rossman–Zhu Proposition 3.16
as stated (missing the "fully symmetric" hypothesis):
`M₃ = E_{(0,0),(0,1)} - E_{(0,1),(0,0)}` has `Q_{M₃} = 0` (`SoS = 0`) while `M₃ ≠ 0` (`PT-rank ≥ 1`). -/
def rzM3 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K :=
  elemM (0, 0) (0, 1) - elemM (0, 1) (0, 0)

theorem rz_prop316_right_counterexample :
    HasSoSFormula (rzM3 (K := K)) 0 ∧ ¬ HasPTRank (rzM3 (K := K)) 0 := by
  constructor
  · refine ⟨0, ?_⟩
    intro a c b d
    unfold biquadCoeff rzM3 elemM
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp
  · rintro ⟨k, B, hk0, _, hsum⟩
    have hk : k = 0 := Nat.eq_zero_of_le_zero hk0
    subst hk
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    have h01 := congrFun (congrFun hsum (0, 0)) (0, 1)
    simp [rzM3, elemM] at h01

end PastaMath.TwoCutSoS
