-- SPDX-License-Identifier: Apache-2.0
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Two-cut (partial-transpose) rank and biquadratic forms: core definitions

This file defines the partial transpose `ptr` on matrices indexed by `Fin r × Fin s`,
two-cut decompositions (`HasTwoCut`), partial-transpose basic matrices (`IsPTBasic`) and
PT-rank (`HasPTRank`), biquadratic evaluation (`qf`), formal biquadratic equivalence
(`SameBiquad`), bilinear product formulas (`HasProdFormula`), and sum-of-squares formulas
(`HasSoSFormula`) over an arbitrary field `K`.
-/

namespace PastaMath.TwoCutSoS

open Matrix Finset

section BasicPtr

variable {K : Type*} {r s : ℕ}

/-- Partial transpose on the second tensor factor:
`(ptr M) (a, b) (c, d) = M (a, d) (c, b)`. -/
def ptr (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    Matrix (Fin r × Fin s) (Fin r × Fin s) K :=
  Matrix.of fun p q => M (p.1, q.2) (q.1, p.2)

@[simp] lemma ptr_apply (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (p q : Fin r × Fin s) : ptr M p q = M (p.1, q.2) (q.1, p.2) := rfl

@[simp] lemma ptr_ptr (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    ptr (ptr M) = M := by
  ext p q; simp

lemma ptr_transpose (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    ptr Mᵀ = (ptr M)ᵀ := by
  ext ⟨a, b⟩ ⟨c, d⟩; rfl

end BasicPtr

variable {K : Type*} [Field K] {r s : ℕ}

@[simp] lemma ptr_zero :
    ptr (0 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) = 0 := by
  ext p q; simp

@[simp] lemma ptr_add (M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    ptr (M + N) = ptr M + ptr N := by
  ext p q; simp

@[simp] lemma ptr_neg (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    ptr (-M) = -ptr M := by
  ext p q; simp

@[simp] lemma ptr_sub (M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    ptr (M - N) = ptr M - ptr N := by
  ext p q; simp

@[simp] lemma ptr_smul (c : K) (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    ptr (c • M) = c • ptr M := by
  ext p q; simp

lemma ptr_sum {ι : Type*} (S : Finset ι)
    (f : ι → Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    ptr (∑ i ∈ S, f i) = ∑ i ∈ S, ptr (f i) := by
  ext p q; simp [Matrix.sum_apply]

@[simp] lemma ptr_one :
    ptr (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [ptr_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2, eq_comm]

/-- A matrix is fully symmetric (in Rossman–Zhu's sense for `d = 2`) if it is invariant under
both transpose and partial transpose. -/
def IsFullySym (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) : Prop :=
  Mᵀ = M ∧ ptr M = M

lemma isFullySym_one :
    IsFullySym (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :=
  ⟨Matrix.transpose_one, ptr_one⟩

/-- Subadditivity of matrix rank. -/
theorem rank_add_le' {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K
          (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule K (m → K)) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- Rank of a finite sum is at most the sum of the ranks. -/
theorem rank_sum_le' {ι m n : Type*} [Fintype m] [Fintype n] [DecidableEq ι]
    (S : Finset ι) (f : ι → Matrix m n K) :
    (∑ i ∈ S, f i).rank ≤ ∑ i ∈ S, (f i).rank := by
  induction S using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le' (f a) (∑ i ∈ S, f i)).trans (Nat.add_le_add_left ih _)

/-- Rank of a scalar multiple is at most the rank. -/
theorem rank_smul_le {m n : Type*} [Fintype m] [Fintype n] (c : K) (A : Matrix m n K) :
    (c • A).rank ≤ A.rank := by
  unfold Matrix.rank
  apply Submodule.finrank_mono
  rintro _ ⟨v, rfl⟩
  refine ⟨c • v, ?_⟩
  ext i
  change (A.mulVec (c • v)) i = ((c • A).mulVec v) i
  simp [Matrix.mulVec_smul, Matrix.smul_mulVec]

/-- A matrix `M` has two-cut rank at most `c` if `M = A + W^Γ` with `rank A + rank W ≤ c`. -/
def HasTwoCut (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (c : ℕ) : Prop :=
  ∃ A W : Matrix (Fin r × Fin s) (Fin r × Fin s) K, A + ptr W = M ∧ A.rank + W.rank ≤ c

/-- A matrix is PT-basic (Rossman–Zhu, `d = 2`) if either `M` or `M^Γ` has rank `1`.
(Since `rank Mᵀ = rank M` and `rank (M^Γ)ᵀ = rank M^Γ`, this covers all four partial
transposes `κ ⊆ {1, 2}`.) -/
def IsPTBasic (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) : Prop :=
  M.rank = 1 ∨ (ptr M).rank = 1

/-- A matrix has PT-rank at most `c` if it is a sum of at most `c` PT-basic matrices. -/
def HasPTRank (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (c : ℕ) : Prop :=
  ∃ (k : ℕ) (B : Fin k → Matrix (Fin r × Fin s) (Fin r × Fin s) K),
    k ≤ c ∧ (∀ i, IsPTBasic (B i)) ∧ ∑ i, B i = M

/-- The biquadratic form `Q_M(x, y) = ∑ M((a,b),(c,d)) x_a y_b x_c y_d`. -/
def qf (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (x : Fin r → K) (y : Fin s → K) : K :=
  ∑ p, ∑ q, M p q * (x p.1 * y p.2) * (x q.1 * y q.2)

theorem qf_ptr (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (x : Fin r → K) (y : Fin s → K) : qf (ptr M) x y = qf M x y := by
  unfold qf
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : (Fin r × Fin s) × (Fin r × Fin s) ≃ (Fin r × Fin s) × (Fin r × Fin s) :=
    { toFun := fun z => ((z.1.1, z.2.2), (z.2.1, z.1.2))
      invFun := fun z => ((z.1.1, z.2.2), (z.2.1, z.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun z => by simp [e]; ring)

theorem qf_transpose (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (x : Fin r → K) (y : Fin s → K) : qf Mᵀ x y = qf M x y := by
  unfold qf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.transpose_apply]; ring

theorem qf_add (M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (x : Fin r → K) (y : Fin s → K) : qf (M + N) x y = qf M x y + qf N x y := by
  unfold qf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.add_apply]; ring

theorem qf_smul (c : K) (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (x : Fin r → K) (y : Fin s → K) : qf (c • M) x y = c * qf M x y := by
  unfold qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

theorem qf_zero (x : Fin r → K) (y : Fin s → K) :
    qf (0 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) x y = 0 := by
  simp [qf]

theorem qf_sum {ι : Type*} (S : Finset ι)
    (f : ι → Matrix (Fin r × Fin s) (Fin r × Fin s) K) (x : Fin r → K) (y : Fin s → K) :
    qf (∑ i ∈ S, f i) x y = ∑ i ∈ S, qf (f i) x y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [qf_zero]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, qf_add, ih]

theorem qf_one (x : Fin r → K) (y : Fin s → K) :
    qf (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) K) x y =
      (∑ a, x a ^ 2) * ∑ b, y b ^ 2 := by
  unfold qf
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun p _ => by ring

theorem qf_vecMulVec (u v : Fin r × Fin s → K) (x : Fin r → K) (y : Fin s → K) :
    qf (Matrix.vecMulVec u v) x y =
      (∑ p, u p * (x p.1 * y p.2)) * ∑ q, v q * (x q.1 * y q.2) := by
  unfold qf
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.vecMulVec_apply]; ring

theorem qf_gram {n : ℕ} (L : Matrix (Fin n) (Fin r × Fin s) K)
    (x : Fin r → K) (y : Fin s → K) :
    qf (Lᵀ * L) x y = ∑ l, (∑ p, L l p * (x p.1 * y p.2)) ^ 2 := by
  have h1 : ∀ l, (∑ p, L l p * (x p.1 * y p.2)) ^ 2 =
      ∑ p, ∑ q, L l p * L l q * (x p.1 * y p.2) * (x q.1 * y q.2) := by
    intro l
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  simp_rw [h1]
  have h2 : qf (Lᵀ * L) x y =
      ∑ p, ∑ q, ∑ l, L l p * L l q * (x p.1 * y p.2) * (x q.1 * y q.2) := by
    unfold qf
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [h2]
  calc ∑ p, ∑ q, ∑ l, L l p * L l q * (x p.1 * y p.2) * (x q.1 * y q.2)
      = ∑ p, ∑ l, ∑ q, L l p * L l q * (x p.1 * y p.2) * (x q.1 * y q.2) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l, ∑ p, ∑ q, L l p * L l q * (x p.1 * y p.2) * (x q.1 * y q.2) := Finset.sum_comm

/-- The four-fold symmetrisation `M + Mᵀ + M^Γ + (M^Γ)ᵀ`, whose entries are the
coefficients of the biquadratic polynomial `Q_M` (scaled by 4 on `x_a² y_b²`, by 2 on
`x_a x_c y_b²` and `x_a² y_b y_d`, and by 1 on `x_a x_c y_b y_d`). -/
def sym4 (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    Matrix (Fin r × Fin s) (Fin r × Fin s) K :=
  M + Mᵀ + ptr M + (ptr M)ᵀ

lemma sym4_add (M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    sym4 (M + N) = sym4 M + sym4 N := by
  unfold sym4; simp only [Matrix.transpose_add, ptr_add]; abel

lemma sym4_smul (c : K) (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    sym4 (c • M) = c • sym4 M := by
  unfold sym4; simp only [Matrix.transpose_smul, ptr_smul, smul_add]

lemma sym4_ptr (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    sym4 (ptr M) = sym4 M := by
  unfold sym4; rw [ptr_ptr]; abel

lemma sym4_transpose (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    sym4 Mᵀ = sym4 M := by
  unfold sym4; rw [Matrix.transpose_transpose, ptr_transpose, Matrix.transpose_transpose]; abel

lemma sym4_of_isFullySym {M : Matrix (Fin r × Fin s) (Fin r × Fin s) K}
    (hM : IsFullySym M) : sym4 M = (4 : K) • M := by
  rcases hM with ⟨hT, hP⟩
  unfold sym4
  rw [hT, hP, hT]
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma qf_sym4 (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (x : Fin r → K) (y : Fin s → K) : qf (sym4 M) x y = 4 * qf M x y := by
  unfold sym4
  rw [qf_add, qf_add, qf_add, qf_transpose, qf_transpose, qf_ptr]
  ring

/-- Exact formal biquadratic coefficient of the monomial `x_a x_c y_b y_d` in `Q_M`:
the sum of the distinct matrix entries contributing to that monomial (`1`, `2`, or `4` terms).
Valid in every characteristic, including characteristic `2`. -/
def biquadCoeff (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (a c : Fin r) (b d : Fin s) : K :=
  if a = c then
    if b = d then M (a, b) (a, b)
    else M (a, b) (a, d) + M (a, d) (a, b)
  else
    if b = d then M (a, b) (c, b) + M (c, b) (a, b)
    else M (a, b) (c, d) + M (c, b) (a, d) + M (a, d) (c, b) + M (c, d) (a, b)

lemma biquadCoeff_add (M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (a c : Fin r) (b d : Fin s) :
    biquadCoeff (M + N) a c b d = biquadCoeff M a c b d + biquadCoeff N a c b d := by
  unfold biquadCoeff
  split_ifs <;> simp only [Matrix.add_apply] <;> ring

lemma biquadCoeff_ptr (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (a c : Fin r) (b d : Fin s) :
    biquadCoeff (ptr M) a c b d = biquadCoeff M a c b d := by
  unfold biquadCoeff
  split_ifs <;> simp only [ptr_apply] <;> ring

lemma biquadCoeff_transpose (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (a c : Fin r) (b d : Fin s) :
    biquadCoeff Mᵀ a c b d = biquadCoeff M a c b d := by
  unfold biquadCoeff
  split_ifs <;> simp only [Matrix.transpose_apply] <;> ring

/-- Formal biquadratic polynomial equality `Q_M = Q_N`: every monomial `x_a x_c y_b y_d`
has the same coefficient in `Q_M` and `Q_N` (valid in every characteristic, including char `2`). -/
def SameBiquad (M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K) : Prop :=
  ∀ a c b d, biquadCoeff M a c b d = biquadCoeff N a c b d

lemma SameBiquad.refl (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    SameBiquad M M := fun _ _ _ _ => rfl

lemma SameBiquad.symm {M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K}
    (h : SameBiquad M N) : SameBiquad N M := fun a c b d => (h a c b d).symm

lemma SameBiquad.trans {L M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K}
    (h1 : SameBiquad L M) (h2 : SameBiquad M N) : SameBiquad L N :=
  fun a c b d => (h1 a c b d).trans (h2 a c b d)

/-- Formal biquadratic equality always implies equality of the four-fold symmetrisations `sym4`. -/
lemma sym4_eq_of_sameBiquad {M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K}
    (h : SameBiquad M N) : sym4 M = sym4 N := by
  ext ⟨a, b⟩ ⟨c, d⟩
  have hab := h a c b d
  unfold biquadCoeff at hab
  unfold sym4
  simp only [Matrix.add_apply, Matrix.transpose_apply, ptr_apply]
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      simp only [if_true] at hab
      linear_combination 4 * hab
    · simp only [if_true, hbd, if_false] at hab
      linear_combination 2 * hab
  · by_cases hbd : b = d
    · subst hbd
      simp only [hac, if_false, if_true] at hab
      linear_combination 2 * hab
    · simp only [hac, hbd, if_false] at hab
      linear_combination hab

/-- Over any field of characteristic ≠ 2, formal biquadratic equality coincides with
equality of the four-fold symmetrisations `sym4 M = sym4 N`. -/
theorem sameBiquad_iff_sym4 (h2 : (2 : K) ≠ 0)
    (M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    SameBiquad M N ↔ sym4 M = sym4 N := by
  constructor
  · exact sym4_eq_of_sameBiquad
  · intro h a c b d
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have hent := congrFun (congrFun h (a, b)) (c, d)
    unfold sym4 at hent
    simp only [Matrix.add_apply, Matrix.transpose_apply, ptr_apply] at hent
    unfold biquadCoeff
    by_cases hac : a = c
    · subst hac
      by_cases hbd : b = d
      · subst hbd
        simp only [if_true]
        apply mul_left_cancel₀ h4
        linear_combination hent
      · simp only [if_true, hbd, if_false]
        apply mul_left_cancel₀ h2
        linear_combination hent
    · by_cases hbd : b = d
      · subst hbd
        simp only [hac, if_false, if_true]
        apply mul_left_cancel₀ h2
        linear_combination hent
      · simp only [hac, hbd, if_false]
        linear_combination hent

/-- Indicator vector on `Fin n`. -/
private def ind {n : ℕ} (i : Fin n) : Fin n → K := fun j => if j = i then 1 else 0

private lemma qf_ind_ind (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (a : Fin r) (b : Fin s) : qf M (ind a) (ind b) = M (a, b) (a, b) := by
  unfold qf ind
  have h1 : ∀ p : Fin r × Fin s, (if p.1 = a then (1 : K) else 0) *
      (if p.2 = b then (1 : K) else 0) = if p = (a, b) then 1 else 0 := by
    rintro ⟨a', b'⟩
    by_cases h1 : a' = a <;> by_cases h2 : b' = b <;> simp [h1, h2]
  simp_rw [h1]
  simp [Finset.sum_ite_eq']

private lemma qf_add_ind_left (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (a c : Fin r) (hac : a ≠ c) (b : Fin s) :
    qf M (ind a + ind c) (ind b) =
      M (a, b) (a, b) + M (c, b) (c, b) + M (a, b) (c, b) + M (c, b) (a, b) := by
  unfold qf ind
  have h1 : ∀ p : Fin r × Fin s,
      ((if p.1 = a then (1 : K) else 0) + (if p.1 = c then (1 : K) else 0)) *
        (if p.2 = b then (1 : K) else 0) =
      (if p = (a, b) then 1 else 0) + (if p = (c, b) then 1 else 0) := by
    rintro ⟨a', b'⟩
    by_cases h1 : a' = a <;> by_cases h2 : a' = c <;> by_cases h3 : b' = b <;>
      simp [h1, h2, h3, hac]
  simp only [Pi.add_apply]
  simp_rw [h1]
  have hinner : ∀ p : Fin r × Fin s,
      ∑ q : Fin r × Fin s,
        M p q * ((if p = (a, b) then (1 : K) else 0) + (if p = (c, b) then 1 else 0)) *
          ((if q = (a, b) then 1 else 0) + (if q = (c, b) then 1 else 0)) =
      (M p (a, b) + M p (c, b)) *
        ((if p = (a, b) then 1 else 0) + (if p = (c, b) then 1 else 0)) := by
    intro p
    have : ∀ q : Fin r × Fin s,
        M p q * ((if p = (a, b) then (1 : K) else 0) + (if p = (c, b) then 1 else 0)) *
          ((if q = (a, b) then 1 else 0) + (if q = (c, b) then 1 else 0)) =
        (if q = (a, b) then M p q * ((if p = (a, b) then 1 else 0) + (if p = (c, b) then 1 else 0)) else 0) +
        (if q = (c, b) then M p q * ((if p = (a, b) then 1 else 0) + (if p = (c, b) then 1 else 0)) else 0) := by
      intro q; split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  simp_rw [hinner]
  have houter : ∀ p : Fin r × Fin s,
      (M p (a, b) + M p (c, b)) *
        ((if p = (a, b) then (1 : K) else 0) + (if p = (c, b) then 1 else 0)) =
      (if p = (a, b) then M p (a, b) + M p (c, b) else 0) +
      (if p = (c, b) then M p (a, b) + M p (c, b) else 0) := by
    intro p; split_ifs <;> ring
  simp_rw [houter]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private lemma qf_add_ind_right (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (a : Fin r) (b d : Fin s) (hbd : b ≠ d) :
    qf M (ind a) (ind b + ind d) =
      M (a, b) (a, b) + M (a, d) (a, d) + M (a, b) (a, d) + M (a, d) (a, b) := by
  unfold qf ind
  have h1 : ∀ p : Fin r × Fin s,
      (if p.1 = a then (1 : K) else 0) *
        ((if p.2 = b then (1 : K) else 0) + (if p.2 = d then (1 : K) else 0)) =
      (if p = (a, b) then 1 else 0) + (if p = (a, d) then 1 else 0) := by
    rintro ⟨a', b'⟩
    by_cases h1 : a' = a <;> by_cases h2 : b' = b <;> by_cases h3 : b' = d <;>
      simp [h1, h2, h3, hbd]
  simp only [Pi.add_apply]
  simp_rw [h1]
  have hinner : ∀ p : Fin r × Fin s,
      ∑ q : Fin r × Fin s,
        M p q * ((if p = (a, b) then (1 : K) else 0) + (if p = (a, d) then 1 else 0)) *
          ((if q = (a, b) then 1 else 0) + (if q = (a, d) then 1 else 0)) =
      (M p (a, b) + M p (a, d)) *
        ((if p = (a, b) then 1 else 0) + (if p = (a, d) then 1 else 0)) := by
    intro p
    have : ∀ q : Fin r × Fin s,
        M p q * ((if p = (a, b) then (1 : K) else 0) + (if p = (a, d) then 1 else 0)) *
          ((if q = (a, b) then 1 else 0) + (if q = (a, d) then 1 else 0)) =
        (if q = (a, b) then M p q * ((if p = (a, b) then 1 else 0) + (if p = (a, d) then 1 else 0)) else 0) +
        (if q = (a, d) then M p q * ((if p = (a, b) then 1 else 0) + (if p = (a, d) then 1 else 0)) else 0) := by
      intro q; split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  simp_rw [hinner]
  have houter : ∀ p : Fin r × Fin s,
      (M p (a, b) + M p (a, d)) *
        ((if p = (a, b) then (1 : K) else 0) + (if p = (a, d) then 1 else 0)) =
      (if p = (a, b) then M p (a, b) + M p (a, d) else 0) +
      (if p = (a, d) then M p (a, b) + M p (a, d) else 0) := by
    intro p; split_ifs <;> ring
  simp_rw [houter]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private lemma qf_add_ind_both (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (a c : Fin r) (hac : a ≠ c) (b d : Fin s) (hbd : b ≠ d) :
    qf M (ind a + ind c) (ind b + ind d) -
      qf M (ind a + ind c) (ind b) - qf M (ind a + ind c) (ind d) -
      qf M (ind a) (ind b + ind d) - qf M (ind c) (ind b + ind d) +
      qf M (ind a) (ind b) + qf M (ind a) (ind d) +
      qf M (ind c) (ind b) + qf M (ind c) (ind d) =
    sym4 M (a, b) (c, d) := by
  have h1 : ∀ p : Fin r × Fin s,
      ((if p.1 = a then (1 : K) else 0) + (if p.1 = c then (1 : K) else 0)) *
        ((if p.2 = b then (1 : K) else 0) + (if p.2 = d then (1 : K) else 0)) =
      (if p = (a, b) then 1 else 0) + (if p = (a, d) then 1 else 0) +
      (if p = (c, b) then 1 else 0) + (if p = (c, d) then 1 else 0) := by
    rintro ⟨a', b'⟩
    by_cases h1 : a' = a <;> by_cases h2 : a' = c <;>
      by_cases h3 : b' = b <;> by_cases h4 : b' = d <;>
      simp [h1, h2, h3, h4, hac, hac.symm, hbd, hbd.symm]
  have hboth : qf M (ind a + ind c) (ind b + ind d) =
      (M (a, b) (a, b) + M (a, b) (a, d) + M (a, b) (c, b) + M (a, b) (c, d)) +
      (M (a, d) (a, b) + M (a, d) (a, d) + M (a, d) (c, b) + M (a, d) (c, d)) +
      (M (c, b) (a, b) + M (c, b) (a, d) + M (c, b) (c, b) + M (c, b) (c, d)) +
      (M (c, d) (a, b) + M (c, d) (a, d) + M (c, d) (c, b) + M (c, d) (c, d)) := by
    unfold qf ind
    simp only [Pi.add_apply]
    simp_rw [h1]
    set S : Finset (Fin r × Fin s) := {(a, b), (a, d), (c, b), (c, d)}
    have hsum : ∀ (f : Fin r × Fin s → K),
        ∑ q : Fin r × Fin s, f q *
          ((if q = (a, b) then (1 : K) else 0) + (if q = (a, d) then 1 else 0) +
           (if q = (c, b) then 1 else 0) + (if q = (c, d) then 1 else 0)) =
        f (a, b) + f (a, d) + f (c, b) + f (c, d) := by
      intro f
      have : ∀ q : Fin r × Fin s,
          f q * ((if q = (a, b) then (1 : K) else 0) + (if q = (a, d) then 1 else 0) +
            (if q = (c, b) then 1 else 0) + (if q = (c, d) then 1 else 0)) =
          (if q = (a, b) then f q else 0) + (if q = (a, d) then f q else 0) +
          (if q = (c, b) then f q else 0) + (if q = (c, d) then f q else 0) := by
        intro q; split_ifs <;> ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq']
    have hinner : ∀ p : Fin r × Fin s,
        ∑ q : Fin r × Fin s, M p q *
          ((if p = (a, b) then (1 : K) else 0) + (if p = (a, d) then 1 else 0) +
           (if p = (c, b) then 1 else 0) + (if p = (c, d) then 1 else 0)) *
          ((if q = (a, b) then 1 else 0) + (if q = (a, d) then 1 else 0) +
           (if q = (c, b) then 1 else 0) + (if q = (c, d) then 1 else 0)) =
        (M p (a, b) + M p (a, d) + M p (c, b) + M p (c, d)) *
          ((if p = (a, b) then 1 else 0) + (if p = (a, d) then 1 else 0) +
           (if p = (c, b) then 1 else 0) + (if p = (c, d) then 1 else 0)) := by
      intro p
      have := hsum (fun q => M p q * ((if p = (a, b) then (1 : K) else 0) +
        (if p = (a, d) then 1 else 0) + (if p = (c, b) then 1 else 0) +
        (if p = (c, d) then 1 else 0)))
      rw [this]; ring
    simp_rw [hinner]
    exact hsum (fun p => M p (a, b) + M p (a, d) + M p (c, b) + M p (c, d))
  rw [hboth, qf_add_ind_left M a c hac b, qf_add_ind_left M a c hac d,
    qf_add_ind_right M a b d hbd, qf_add_ind_right M c b d hbd,
    qf_ind_ind, qf_ind_ind, qf_ind_ind, qf_ind_ind]
  unfold sym4
  simp only [Matrix.add_apply, Matrix.transpose_apply, ptr_apply]
  ring

private lemma sum_pair_split {n : ℕ} (f : Fin n → Fin n → K) :
    ∑ i : Fin n, ∑ j : Fin n, f i j =
      (∑ i : Fin n, f i i) +
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (f i j + f j i) := by
  have h1 : ∀ i : Fin n, ∑ j : Fin n, f i j =
      f i i + (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f i j) +
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), f i j) := by
    intro i
    have hdisj1 : Disjoint (Finset.univ.filter (fun j : Fin n => i < j))
        (Finset.univ.filter (fun j : Fin n => j < i)) := by
      rw [Finset.disjoint_filter]; intro j _ hlt hgt; exact lt_asymm hlt hgt
    have hdisj2 : Disjoint ({i} : Finset (Fin n))
        (Finset.univ.filter (fun j : Fin n => i < j) ∪
         Finset.univ.filter (fun j : Fin n => j < i)) := by
      simp only [Finset.disjoint_singleton_left, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, lt_self_iff_false, or_self, not_false_eq_true]
    have hunion : ({i} : Finset (Fin n)) ∪
        (Finset.univ.filter (fun j : Fin n => i < j) ∪
         Finset.univ.filter (fun j : Fin n => j < i)) = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact Or.inr (Or.inl hlt)
      · exact Or.inl heq.symm
      · exact Or.inr (Or.inr hgt)
    calc ∑ j : Fin n, f i j
        = ∑ j ∈ ({i} ∪ (Finset.univ.filter (fun j : Fin n => i < j) ∪
            Finset.univ.filter (fun j : Fin n => j < i))), f i j := by rw [hunion]
      _ = f i i + ((∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f i j) +
            (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), f i j)) := by
          rw [Finset.sum_union hdisj2, Finset.sum_singleton, Finset.sum_union hdisj1]
      _ = _ := by ring
  simp_rw [h1, Finset.sum_add_distrib]
  have hswap : ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), f i j =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f j i := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  have hcomb : (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f i j) +
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f j i) =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (f i j + f j i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm
  rw [add_assoc, hcomb]

private lemma qf_eq_sum_biquadCoeff (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (x : Fin r → K) (y : Fin s → K) :
    qf M x y =
      ((∑ a : Fin r, ∑ b : Fin s, biquadCoeff M a a b b * (x a * x a * (y b * y b))) +
       (∑ a : Fin r, ∑ b : Fin s, ∑ d ∈ Finset.univ.filter (fun d : Fin s => b < d),
         biquadCoeff M a a b d * (x a * x a * (y b * y d)))) +
      ((∑ a : Fin r, ∑ c ∈ Finset.univ.filter (fun c : Fin r => a < c), ∑ b : Fin s,
         biquadCoeff M a c b b * (x a * x c * (y b * y b))) +
       (∑ a : Fin r, ∑ c ∈ Finset.univ.filter (fun c : Fin r => a < c),
         ∑ b : Fin s, ∑ d ∈ Finset.univ.filter (fun d : Fin s => b < d),
         biquadCoeff M a c b d * (x a * x c * (y b * y d)))) := by
  have hreord : qf M x y = ∑ a : Fin r, ∑ c : Fin r, ∑ b : Fin s, ∑ d : Fin s,
      M (a, b) (c, d) * (x a * x c * (y b * y d)) := by
    unfold qf
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun d _ => by ring
  rw [hreord, sum_pair_split (fun a c => ∑ b : Fin s, ∑ d : Fin s,
      M (a, b) (c, d) * (x a * x c * (y b * y d)))]
  congr 1
  · have hdiag : ∀ a : Fin r,
        (∑ b : Fin s, ∑ d : Fin s, M (a, b) (a, d) * (x a * x a * (y b * y d))) =
        (∑ b : Fin s, biquadCoeff M a a b b * (x a * x a * (y b * y b))) +
        (∑ b : Fin s, ∑ d ∈ Finset.univ.filter (fun d : Fin s => b < d),
          biquadCoeff M a a b d * (x a * x a * (y b * y d))) := by
      intro a
      rw [sum_pair_split (fun b d => M (a, b) (a, d) * (x a * x a * (y b * y d)))]
      congr 1
      · refine Finset.sum_congr rfl fun b _ => ?_
        simp [biquadCoeff]
      · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d hd => ?_
        have hbd : b ≠ d := ne_of_lt (Finset.mem_filter.1 hd).2
        simp only [biquadCoeff, if_true, hbd, if_false]; ring
    simp_rw [hdiag, Finset.sum_add_distrib]
  · have hoff : ∀ a : Fin r, ∀ c ∈ Finset.univ.filter (fun c : Fin r => a < c),
        ((∑ b : Fin s, ∑ d : Fin s, M (a, b) (c, d) * (x a * x c * (y b * y d))) +
         (∑ b : Fin s, ∑ d : Fin s, M (c, b) (a, d) * (x c * x a * (y b * y d)))) =
        (∑ b : Fin s, biquadCoeff M a c b b * (x a * x c * (y b * y b))) +
        (∑ b : Fin s, ∑ d ∈ Finset.univ.filter (fun d : Fin s => b < d),
          biquadCoeff M a c b d * (x a * x c * (y b * y d))) := by
      intro a c hc
      have hac : a ≠ c := ne_of_lt (Finset.mem_filter.1 hc).2
      rw [← Finset.sum_add_distrib]
      have hmerge : ∀ b : Fin s,
          (∑ d : Fin s, M (a, b) (c, d) * (x a * x c * (y b * y d))) +
          (∑ d : Fin s, M (c, b) (a, d) * (x c * x a * (y b * y d))) =
          ∑ d : Fin s, (M (a, b) (c, d) + M (c, b) (a, d)) * (x a * x c * (y b * y d)) := by
        intro b
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => by ring
      simp_rw [hmerge]
      rw [sum_pair_split (fun b d => (M (a, b) (c, d) + M (c, b) (a, d)) * (x a * x c * (y b * y d)))]
      congr 1
      · refine Finset.sum_congr rfl fun b _ => ?_
        simp only [biquadCoeff, hac, if_false, if_true]
      · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d hd => ?_
        have hbd : b ≠ d := ne_of_lt (Finset.mem_filter.1 hd).2
        simp only [biquadCoeff, hac, hbd, if_false]; ring
    have houter : ∀ a : Fin r,
        (∑ c ∈ Finset.univ.filter (fun c : Fin r => a < c),
          ((∑ b : Fin s, ∑ d : Fin s, M (a, b) (c, d) * (x a * x c * (y b * y d))) +
           (∑ b : Fin s, ∑ d : Fin s, M (c, b) (a, d) * (x c * x a * (y b * y d))))) =
        (∑ c ∈ Finset.univ.filter (fun c : Fin r => a < c),
          ∑ b : Fin s, biquadCoeff M a c b b * (x a * x c * (y b * y b))) +
        (∑ c ∈ Finset.univ.filter (fun c : Fin r => a < c),
          ∑ b : Fin s, ∑ d ∈ Finset.univ.filter (fun d : Fin s => b < d),
          biquadCoeff M a c b d * (x a * x c * (y b * y d))) := by
      intro a
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c hc => hoff a c hc
    simp_rw [houter, Finset.sum_add_distrib]

/-- Over every field `K` (including characteristic `2`), formal biquadratic equivalence
(`SameBiquad M N`) coincides with pointwise equality of `qf M` and `qf N`. -/
theorem sameBiquad_iff_qf
    (M N : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    SameBiquad M N ↔ ∀ x y, qf M x y = qf N x y := by
  constructor
  · intro h x y
    rw [qf_eq_sum_biquadCoeff M, qf_eq_sum_biquadCoeff N]
    dsimp only [SameBiquad] at h
    simp_rw [h]
  · intro h a c b d
    unfold biquadCoeff
    by_cases hac : a = c
    · subst hac
      by_cases hbd : b = d
      · subst hbd
        simp only [if_true]
        have hab := h (ind a) (ind b)
        rwa [qf_ind_ind, qf_ind_ind] at hab
      · simp only [if_true, hbd, if_false]
        have h1 := h (ind a) (ind b + ind d)
        have h2a := h (ind a) (ind b)
        have h2b := h (ind a) (ind d)
        rw [qf_add_ind_right M a b d hbd, qf_add_ind_right N a b d hbd] at h1
        rw [qf_ind_ind, qf_ind_ind] at h2a h2b
        linear_combination h1 - h2a - h2b
    · by_cases hbd : b = d
      · subst hbd
        simp only [hac, if_false, if_true]
        have h1 := h (ind a + ind c) (ind b)
        have h2a := h (ind a) (ind b)
        have h2b := h (ind c) (ind b)
        rw [qf_add_ind_left M a c hac b, qf_add_ind_left N a c hac b] at h1
        rw [qf_ind_ind, qf_ind_ind] at h2a h2b
        linear_combination h1 - h2a - h2b
      · simp only [hac, hbd, if_false]
        have hboth := qf_add_ind_both M a c hac b d hbd
        have hbothN := qf_add_ind_both N a c hac b d hbd
        have heq : sym4 M (a, b) (c, d) = sym4 N (a, b) (c, d) := by
          rw [← hboth, ← hbothN]; simp only [h]
        unfold sym4 at heq
        simp only [Matrix.add_apply, Matrix.transpose_apply, ptr_apply] at heq
        linear_combination heq

/-- `Q_M` admits a bilinear product formula of size `n`:
`Q_M(x, y) = ∑_{l < n} f_l(x, y) g_l(x, y)` (formally, via `SameBiquad`). -/
def HasProdFormula (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (n : ℕ) : Prop :=
  ∃ u v : Fin n → Fin r × Fin s → K,
    SameBiquad (∑ l, Matrix.vecMulVec (u l) (v l)) M

/-- `Q_M` admits a sum-of-squares formula of size `n`:
`Q_M(x, y) = ∑_{l < n} f_l(x, y)²` (formally, via `SameBiquad`). -/
def HasSoSFormula (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (n : ℕ) : Prop :=
  ∃ L : Matrix (Fin n) (Fin r × Fin s) K, SameBiquad (Lᵀ * L) M

/-- Pointwise characterisation of `HasProdFormula` over every field `K`. -/
theorem hasProdFormula_iff_qf
    (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (n : ℕ) :
    HasProdFormula M n ↔
      ∃ u v : Fin n → Fin r × Fin s → K,
        ∀ x y, (∑ l, (∑ p, u l p * (x p.1 * y p.2)) * ∑ q, v l q * (x q.1 * y q.2)) =
          qf M x y := by
  constructor
  · rintro ⟨u, v, h⟩
    refine ⟨u, v, fun x y => ?_⟩
    have hq := (sameBiquad_iff_qf _ _).1 h x y
    rw [qf_sum] at hq
    simpa [qf_vecMulVec] using hq
  · rintro ⟨u, v, h⟩
    refine ⟨u, v, (sameBiquad_iff_qf _ _).2 fun x y => ?_⟩
    rw [qf_sum]
    simpa [qf_vecMulVec] using h x y

/-- Pointwise characterisation of `HasSoSFormula` over every field `K`. -/
theorem hasSoSFormula_iff_qf
    (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) (n : ℕ) :
    HasSoSFormula M n ↔
      ∃ L : Matrix (Fin n) (Fin r × Fin s) K,
        ∀ x y, (∑ l, (∑ p, L l p * (x p.1 * y p.2)) ^ 2) = qf M x y := by
  constructor
  · rintro ⟨L, h⟩
    refine ⟨L, fun x y => ?_⟩
    have hq := (sameBiquad_iff_qf _ _).1 h x y
    rwa [qf_gram] at hq
  · rintro ⟨L, h⟩
    refine ⟨L, (sameBiquad_iff_qf _ _).2 fun x y => ?_⟩
    rw [qf_gram]
    exact h x y

end PastaMath.TwoCutSoS
