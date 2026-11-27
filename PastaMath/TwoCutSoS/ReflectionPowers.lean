-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import PastaMath.TwoCutSoS.LowerBounds

/-!
# Reflection-type word-span tensor powers

This file formalises the weighted uncertainty framework for word-span decompositions of tensor
powers of reflection-type two-cut decompositions (`spec M = {0^(D-n), λ^n}`,
`spec M^Γ = {1^(D-n), (1-λ)^n}` with `D = r * s`, `p = n / D`, `λ = 1 / (2p)`):

1. **The `p`-biased reflection operator `T_{-1}`**: `reflE`, `reflOp`, `muP`, proving involution
   (`reflOp_involutive`), self-adjointness in `L²(μ_p)` (`reflOp_selfadjoint`), constant fixation
   (`reflOp_const_one`), `p ↔ 1 - p` duality (`wordSpanCost_one_sub`), and the exact trace and
   slice constraints for reflection-type matrices (`trace_ptr`, `reflection_lam_eq`,
   `reflection_slice_constraint`, `wordPoly_eval_B`).
2. **The Valuation Theorem** (`valuation_theorem`, `layer_grouping_le`): when `λ = a / b` with a
   prime `ℓ ∣ a - b` and `ℓ ∤ a`, every word-span linear combination with `ℓ`-integral coefficients
   costs at least the Bayes error `∑_T min(μ_p(T), μ_{1-p}(T))`, attained exactly at every `K` by
   the layer grouping.
3. **Tensorising Farkas-certificate packings**: `ReflCert`, `CertPacking`, `CertPacking.lower_bound`,
   `CertPacking.tensor`, `CertPacking.asymptotic_bound`.
4. **Explicit packings**:
   - `packing_K1_trivial` (any `p ∈ (0, 1)`),
   - `packing_K1_mid` (`p ∈ [1/3, 2/3]`, value `2/3`),
   - `packing_K2` (`p ∈ (0, 1/2]`, value `min (2p - p²) ((1 - p)²)`),
   - `packing_K4_quarter` (`p = 1/4`, 22 exact rational certificates of total value `57/256`,
     checked by pure kernel `decide`).
5. **Reflection-type word-span no-go theorem** (`reflection_wordSpan_nogo`): for every shape
   `r, s ≥ 2` and every reflection-type weight `p = n / (r * s)` satisfying the slice constraint
   `max r s ≤ 2 * min n (r * s - n)`, there exist `c > 0` and `g > 0` with
   `Real.log (r * s * g) > √((Real.log r)² + (Real.log s)²)` such that every `K` and every
   word-span evaluation `h : (Fin K → Bool) → ℝ` satisfies
   `c * (r * s * g) ^ K ≤ (r * s : ℝ) ^ K * wordSpanCost p h`.
-/

namespace PastaMath.TwoCutSoS

open scoped BigOperators
open Matrix

section ReflectionOperator

/-- Single-slot `p`-biased Bernoulli weight: `false ↦ 1 - p`, `true ↦ p`. -/
def slotWeight (p : ℝ) (b : Bool) : ℝ :=
  if b then p else 1 - p

/-- Product measure `μ_p` on `{false, true}^K`. -/
def muP (p : ℝ) {K : ℕ} (x : Fin K → Bool) : ℝ :=
  ∏ i : Fin K, slotWeight p (x i)

theorem slotWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ slotWeight p b := by
  cases b <;> simp [slotWeight] <;> linarith

theorem muP_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {K : ℕ} (x : Fin K → Bool) :
    0 ≤ muP p x :=
  Finset.prod_nonneg fun i _ => slotWeight_nonneg hp0 hp1 (x i)

theorem slotWeight_one_sub (p : ℝ) (b : Bool) :
    slotWeight (1 - p) b = slotWeight p (!b) := by
  cases b <;> simp [slotWeight]

theorem muP_one_sub (p : ℝ) {K : ℕ} (x : Fin K → Bool) :
    muP (1 - p) x = muP p (fun i => !(x i)) := by
  simp only [muP, slotWeight_one_sub]

/-- Single-slot reflection kernel `E₁(p) = [[1 - 2p, 2p], [2 - 2p, 2p - 1]]`
(rows indexed by `b`, columns by `a`). -/
def reflE (p : ℝ) (b a : Bool) : ℝ :=
  match b, a with
  | false, false => 1 - 2 * p
  | false, true => 2 * p
  | true, false => 2 - 2 * p
  | true, true => 2 * p - 1

theorem reflE_mul_reflE (p : ℝ) (b a : Bool) :
    ∑ c : Bool, reflE p b c * reflE p c a = if b = a then 1 else 0 := by
  cases b <;> cases a <;> simp [reflE] <;> ring

theorem reflE_selfadjoint (p : ℝ) (b a : Bool) :
    slotWeight p b * reflE p b a = slotWeight p a * reflE p a b := by
  cases b <;> cases a <;> simp [slotWeight, reflE] <;> ring

theorem reflE_row_sum (p : ℝ) (b : Bool) :
    ∑ a : Bool, reflE p b a = 1 := by
  cases b <;> (simp [reflE]; try ring)

theorem reflE_one_sub (p : ℝ) (b a : Bool) :
    reflE (1 - p) b a = reflE p (!b) (!a) := by
  cases b <;> cases a <;> simp [reflE] <;> ring

/-- Tensor reflection operator `T_{-1} = E₁(p)^{⊗K}` acting on functions `{false, true}^K → ℝ`. -/
def reflOp (p : ℝ) {K : ℕ} (h : (Fin K → Bool) → ℝ) (y : Fin K → Bool) : ℝ :=
  ∑ x : Fin K → Bool, (∏ i : Fin K, reflE p (y i) (x i)) * h x

/-- Transpose of `reflOp p`: `(E₁(p)ᵀ)^{⊗K}` mapping B-grid vectors to A-grid vectors. -/
def reflOpT (p : ℝ) {K : ℕ} (y : (Fin K → Bool) → ℝ) (a : Fin K → Bool) : ℝ :=
  ∑ b : Fin K → Bool, (∏ i : Fin K, reflE p (b i) (a i)) * y b

/-- Adjoint identity `⟨y, reflOp p h⟩ = ⟨reflOpT p y, h⟩`. -/
theorem sum_mul_reflOp (p : ℝ) {K : ℕ} (y h : (Fin K → Bool) → ℝ) :
    ∑ b : Fin K → Bool, y b * reflOp p h b =
    ∑ a : Fin K → Bool, reflOpT p y a * h a := by
  simp only [reflOp, reflOpT, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- `T_{-1}` is an involution: `reflOp p (reflOp p h) = h`. -/
theorem reflOp_involutive (p : ℝ) {K : ℕ} (h : (Fin K → Bool) → ℝ) :
    reflOp p (reflOp p h) = h := by
  ext y
  simp only [reflOp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ x : Fin K → Bool,
      ∑ z : Fin K → Bool, (∏ i : Fin K, reflE p (y i) (z i)) *
        ((∏ i : Fin K, reflE p (z i) (x i)) * h x) =
      if y = x then h x else 0 := by
    intro x
    have hpull : ∀ z : Fin K → Bool,
        (∏ i : Fin K, reflE p (y i) (z i)) *
          ((∏ i : Fin K, reflE p (z i) (x i)) * h x) =
        (∏ i : Fin K, (reflE p (y i) (z i) * reflE p (z i) (x i))) * h x := by
      intro z; rw [← mul_assoc, ← Finset.prod_mul_distrib]
    simp_rw [hpull, ← Finset.sum_mul]
    rw [← Fintype.prod_sum (fun i c => reflE p (y i) c * reflE p c (x i))]
    have hprod : ∏ i : Fin K, ∑ c : Bool, reflE p (y i) c * reflE p c (x i) =
        if y = x then 1 else 0 := by
      simp_rw [reflE_mul_reflE]
      by_cases hyx : y = x
      · subst hyx; simp
      · simp only [hyx, ↓reduceIte]
        have ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
          by_contra hall; push Not at hall; exact hyx (funext hall)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hprod]
    split_ifs <;> ring
  simp_rw [hinner]
  simp

/-- `T_{-1}` is self-adjoint in `L²(μ_p)`. -/
theorem reflOp_selfadjoint (p : ℝ) {K : ℕ} (f g : (Fin K → Bool) → ℝ) :
    ∑ y : Fin K → Bool, muP p y * f y * reflOp p g y =
    ∑ x : Fin K → Bool, muP p x * reflOp p f x * g x := by
  simp only [reflOp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hsym : muP p y * (∏ i : Fin K, reflE p (y i) (x i)) =
      muP p x * (∏ i : Fin K, reflE p (x i) (y i)) := by
    simp only [muP, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => reflE_selfadjoint p (y i) (x i)
  calc muP p y * f y * ((∏ i : Fin K, reflE p (y i) (x i)) * g x)
      = (muP p y * ∏ i : Fin K, reflE p (y i) (x i)) * (f y * g x) := by ring
    _ = (muP p x * ∏ i : Fin K, reflE p (x i) (y i)) * (f y * g x) := by rw [hsym]
    _ = muP p x * ((∏ i : Fin K, reflE p (x i) (y i)) * f y) * g x := by ring

/-- `T_{-1}` fixes the constant function `1`. -/
theorem reflOp_const_one (p : ℝ) {K : ℕ} :
    reflOp p (fun _ : Fin K → Bool => (1 : ℝ)) = fun _ => 1 := by
  ext y
  simp only [reflOp, mul_one]
  rw [← Fintype.prod_sum (fun i a => reflE p (y i) a)]
  exact Finset.prod_eq_one fun i _ => reflE_row_sum p (y i)

/-- Normalised word-span cost `φ_K(p; h) = μ_p(supp h) + μ_p(supp (1 - T_{-1} h))`. -/
noncomputable def wordSpanCost (p : ℝ) {K : ℕ} (h : (Fin K → Bool) → ℝ) : ℝ :=
  (∑ x : Fin K → Bool, if h x ≠ 0 then muP p x else 0) +
  (∑ y : Fin K → Bool, if reflOp p h y ≠ 1 then muP p y else 0)

/-- `p ↔ 1 - p` symmetry of `wordSpanCost`. -/
theorem wordSpanCost_one_sub (p : ℝ) {K : ℕ} (h : (Fin K → Bool) → ℝ) :
    wordSpanCost (1 - p) h = wordSpanCost p (fun x => h (fun i => !(x i))) := by
  let flip : (Fin K → Bool) ≃ (Fin K → Bool) :=
    { toFun := fun x i => !(x i)
      invFun := fun x i => !(x i)
      left_inv := fun x => by ext i; simp
      right_inv := fun x => by ext i; simp }
  have hrefl : ∀ y, reflOp (1 - p) h y = reflOp p (fun x => h (flip x)) (flip y) := by
    intro y
    simp only [reflOp]
    rw [← Equiv.sum_comp flip
      (fun x => (∏ i : Fin K, reflE (1 - p) (y i) (x i)) * h x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [flip, reflE_one_sub]
  simp only [wordSpanCost, muP_one_sub]
  congr 1
  · rw [← Equiv.sum_comp flip (fun x => if h x ≠ 0 then muP p (fun i => !(x i)) else 0)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hff : (fun i => !(flip x i)) = x := by ext i; simp [flip]
    rw [hff]; rfl
  · rw [← Equiv.sum_comp flip
      (fun y => if reflOp (1 - p) h y ≠ 1 then muP p (fun i => !(y i)) else 0)]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h1 := hrefl (flip y)
    have h2 : flip (flip y) = y := flip.apply_symm_apply y
    have hff : (fun i => !(flip y i)) = y := by ext i; simp [flip]
    rw [h2] at h1
    rw [hff, h1]; rfl

end ReflectionOperator

section MatrixBridge

/-- Partial transpose preserves trace: `tr (ptr M) = tr M`. -/
theorem trace_ptr {r s : ℕ} {K : Type*} [CommRing K]
    (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K) :
    Matrix.trace (ptr M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, ptr_apply]

/-- Trace identity for reflection-type spectra:
`tr M = λ n` and `tr M^Γ = (D - n) · 1 + n · (1 - λ)` force `2 λ n = D`. -/
theorem reflection_lam_eq {lam n D : ℝ}
    (htr : lam * n = (D - n) * 1 + n * (1 - lam)) :
    2 * lam * n = D := by
  linarith

/-- Multilinear word-span polynomial `F(x) = ∑_w c_w ∏_i (if w i then x i else 1 - x i)`. -/
def wordPoly {K : ℕ} {R : Type*} [CommRing R] (c : (Fin K → Bool) → R)
    (x : Fin K → R) : R :=
  ∑ w : Fin K → Bool, c w * ∏ i : Fin K, if w i then x i else 1 - x i

/-- On reflection-type spectra (`λ = 1/(2p)`), evaluating a multilinear word polynomial at the
`B`-eigenvalues `1 - λ b_i` equals `T_{-1}` applied to its `A`-eigenvalues `λ a_i`. -/
theorem wordPoly_eval_B {K : ℕ} {p lam : ℝ} (hpl : 2 * p * lam = 1)
    (c : (Fin K → Bool) → ℝ) (b : Fin K → Bool) :
    wordPoly c (fun i => if b i then 1 - lam else 1) =
    reflOp p (fun a => wordPoly c (fun i => if a i then lam else 0)) b := by
  simp only [reflOp, wordPoly, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hpull : ∀ a : Fin K → Bool,
      (∏ i : Fin K, reflE p (b i) (a i)) *
        (c w * ∏ i : Fin K, if w i then (if a i then lam else 0) else 1 - (if a i then lam else 0)) =
      c w * ∏ i : Fin K, (reflE p (b i) (a i) *
        (if w i then (if a i then lam else 0) else 1 - (if a i then lam else 0))) := by
    intro a
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
  simp_rw [hpull, ← Finset.mul_sum]
  congr 1
  symm
  rw [← Fintype.prod_sum (fun i a =>
    reflE p (b i) a * (if w i then (if a then lam else 0) else 1 - (if a then lam else 0)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases w i <;> cases b i <;> simp [reflE] <;>
    first | linear_combination hpl | linear_combination -hpl

/-- Slice constraint for a reflection-type matrix `M` over `ℝ`:
if `M` is similar to `diag(0^(D-n), λ^n)` and `ptr M` is similar to `diag(1^(D-n), (1-λ)^n)`
with `0 < n < r * s`, then `max r s ≤ 2 * min n (r * s - n)`. -/
theorem reflection_slice_constraint {r s n : ℕ} {lam : ℝ}
    (hn0 : 0 < n) (hnD : n < r * s)
    (M : Matrix (Fin r × Fin s) (Fin r × Fin s) ℝ)
    (vA vB : Fin r × Fin s → Bool)
    (hvA : (Finset.univ.filter fun u => vA u = true).card = n)
    (hvB : (Finset.univ.filter fun u => vB u = true).card = n)
    (SA SB : (Matrix (Fin r × Fin s) (Fin r × Fin s) ℝ)ˣ)
    (hSA : SA.val * M * SA.inv = Matrix.diagonal (fun u => if vA u then lam else 0))
    (hSB : SB.val * ptr M * SB.inv = Matrix.diagonal (fun u => if vB u then 1 - lam else 1)) :
    max r s ≤ 2 * min n (r * s - n) := by
  have hrs_pos : 0 < r * s := lt_trans hn0 hnD
  have hr0 : 0 < r := Nat.pos_of_mul_pos_right hrs_pos
  have hs0 : 0 < s := Nat.pos_of_mul_pos_left hrs_pos
  have hD_pos : (0 : ℝ) < (r * s : ℕ) := by exact_mod_cast hrs_pos
  have htrA : Matrix.trace M = lam * (n : ℝ) := by
    have h1 : Matrix.trace (SA.val * M * SA.inv) = Matrix.trace M := by
      rw [Matrix.trace_mul_cycle, SA.inv_val, Matrix.one_mul]
    rw [← h1, hSA, Matrix.trace_diagonal]
    have : ∑ u : Fin r × Fin s, (if vA u = true then lam else 0) =
        ((Finset.univ.filter fun u => vA u = true).card : ℝ) * lam := by
      simp [Finset.sum_ite]
    rw [this, hvA]; ring
  have htrB : Matrix.trace (ptr M) = ((r * s : ℕ) - (n : ℝ)) * 1 + (n : ℝ) * (1 - lam) := by
    have h1 : Matrix.trace (SB.val * ptr M * SB.inv) = Matrix.trace (ptr M) := by
      rw [Matrix.trace_mul_cycle, SB.inv_val, Matrix.one_mul]
    rw [← h1, hSB, Matrix.trace_diagonal]
    have hsum : ∑ u : Fin r × Fin s, (if vB u = true then (1 - lam) else (1 : ℝ)) =
        ((Finset.univ.filter fun u => vB u = true).card : ℝ) * (1 - lam) +
        ((Finset.univ.filter fun u => ¬ vB u = true).card : ℝ) * 1 := by
      rw [Finset.sum_ite]; simp [Finset.sum_const]; ring
    have hcomp : n + (Finset.univ.filter fun u => ¬ vB u = true).card = r * s := by
      rw [← hvB, Finset.card_filter_add_card_filter_not]
      simp [Fintype.card_prod, Fintype.card_fin]
    rw [hsum, hvB]
    have hcompR : (n : ℝ) + ((Finset.univ.filter fun u => ¬ vB u = true).card : ℝ) = (r * s : ℕ) := by
      exact_mod_cast hcomp
    linarith
  have h2lam : 2 * lam * (n : ℝ) = (r * s : ℕ) :=
    reflection_lam_eq (by rw [← htrA, ← htrB, trace_ptr])
  have hlam_ne : lam ≠ 0 := by
    intro h0; rw [h0] at h2lam; linarith
  have rank_of_sim : ∀ (X : Matrix (Fin r × Fin s) (Fin r × Fin s) ℝ)
      (S : (Matrix (Fin r × Fin s) (Fin r × Fin s) ℝ)ˣ)
      (d : Fin r × Fin s → ℝ),
      S.val * X * S.inv = Matrix.diagonal d →
      X.rank ≤ (Finset.univ.filter fun u => d u ≠ 0).card := by
    intro X S d hS
    have hX : X = S.inv * Matrix.diagonal d * S.val := by
      calc X = 1 * X * 1 := by simp
        _ = (S.inv * S.val) * X * (S.inv * S.val) := by rw [S.inv_val]
        _ = S.inv * (S.val * X * S.inv) * S.val := by simp [Matrix.mul_assoc]
        _ = S.inv * Matrix.diagonal d * S.val := by rw [hS]
    rw [hX]
    calc (S.inv * Matrix.diagonal d * S.val).rank
        ≤ (S.inv * Matrix.diagonal d).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (Matrix.diagonal d).rank := Matrix.rank_mul_le_right _ _
      _ ≤ (Finset.univ.filter fun u => d u ≠ 0).card := by
          have hdecomp : Matrix.diagonal d =
              ∑ u ∈ Finset.univ.filter (fun u => d u ≠ 0),
                Matrix.vecMulVec (Pi.single u (d u)) (Pi.single u (1 : ℝ)) := by
            ext a b
            simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
              Pi.single_apply]
            by_cases hab : a = b
            · subst hab
              by_cases hda : d a = 0
              · simp only [↓reduceIte, hda]
                refine (Finset.sum_eq_zero fun u hu => ?_).symm
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
                have hua : a ≠ u := fun h => hu (h ▸ hda)
                simp [hua]
              · simp only [↓reduceIte]
                rw [Finset.sum_eq_single a]
                · simp
                · intro u _ hua; simp [Ne.symm hua]
                · intro ha; simp [hda] at ha
            · simp only [hab, ↓reduceIte]
              refine (Finset.sum_eq_zero fun u _ => ?_).symm
              by_cases hau : a = u
              · subst hau; simp [Ne.symm hab]
              · simp [hau]
          rw [hdecomp]
          calc (∑ u ∈ Finset.univ.filter (fun u => d u ≠ 0),
                Matrix.vecMulVec (Pi.single u (d u)) (Pi.single u (1 : ℝ))).rank
              ≤ ∑ u ∈ Finset.univ.filter (fun u => d u ≠ 0),
                  (Matrix.vecMulVec (Pi.single u (d u)) (Pi.single u (1 : ℝ))).rank :=
                rank_sum_le' _ _
            _ ≤ ∑ _u ∈ Finset.univ.filter (fun u => d u ≠ 0), 1 :=
                Finset.sum_le_sum fun u _ => Matrix.rank_vecMulVec_le _ _
            _ = (Finset.univ.filter fun u => d u ≠ 0).card := by simp
  have htc1 : HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) ℝ) (2 * n) := by
    refine ⟨M, ptr (1 - M), by rw [ptr_ptr]; abel, ?_⟩
    have hrM : M.rank ≤ n := by
      calc M.rank ≤ (Finset.univ.filter fun u => (if vA u then lam else 0) ≠ 0).card :=
            rank_of_sim M SA _ hSA
        _ = n := by
            rw [← hvA]; congr 1; ext u; cases vA u <;> simp [hlam_ne]
    have hSB1 : SB.val * ptr (1 - M) * SB.inv =
        Matrix.diagonal (fun u => if vB u then lam else 0) := by
      rw [ptr_sub, ptr_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, SB.val_inv, hSB]
      ext a b
      by_cases hab : a = b
      · subst hab; cases hv : vB a <;> simp [hv]
      · simp [hab]
    have hrW : (ptr (1 - M)).rank ≤ n := by
      calc (ptr (1 - M)).rank ≤ (Finset.univ.filter fun u => (if vB u then lam else 0) ≠ 0).card :=
            rank_of_sim (ptr (1 - M)) SB _ hSB1
        _ = n := by
            rw [← hvB]; congr 1; ext u; cases vB u <;> simp [hlam_ne]
    omega
  have htc2 : HasTwoCut (1 : Matrix (Fin r × Fin s) (Fin r × Fin s) ℝ) (2 * (r * s - n)) := by
    have h2l1 : 2 * lam - 1 ≠ 0 := by
      have hpos : (0 : ℝ) < (r * s : ℕ) - n := by
        have : (n : ℝ) < (r * s : ℕ) := by exact_mod_cast hnD
        linarith
      intro h0
      have : (2 * lam - 1) * n = (r * s : ℕ) - n := by linarith
      rw [h0, zero_mul] at this; linarith
    let α : ℝ := lam / (2 * lam - 1)
    let P' : Matrix (Fin r × Fin s) (Fin r × Fin s) ℝ := α • (1 - lam⁻¹ • M)
    refine ⟨P', ptr (1 - P'), by rw [ptr_ptr]; abel, ?_⟩
    have hSA' : SA.val * P' * SA.inv = Matrix.diagonal (fun u => if vA u then 0 else α) := by
      simp only [P', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, SA.val_inv, hSA]
      ext a b
      by_cases hab : a = b
      · subst hab; cases hv : vA a <;> simp [hv, hlam_ne]
      · simp [hab]
    have hSB' : SB.val * ptr (1 - P') * SB.inv =
        Matrix.diagonal (fun u => if vB u then 0 else 1 - α * (1 - lam⁻¹)) := by
      have hptrP' : ptr P' = α • (1 - lam⁻¹ • ptr M) := by
        simp only [P', ptr_smul, ptr_sub, ptr_one]
      rw [ptr_sub, ptr_one, hptrP']
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, SB.val_inv, hSB]
      ext a b
      by_cases hab : a = b
      · subst hab
        cases hv : vB a
        · simp [hv]
        · have h2l1' : -1 + lam * 2 ≠ 0 := fun h => h2l1 (by linarith)
          simp [hv]; dsimp only [α]
          field_simp [hlam_ne, h2l1, h2l1']
          linear_combination -(inv_mul_cancel₀ h2l1')
      · simp [hab]
    have hcompA : (Finset.univ.filter fun u => ¬ vA u = true).card = r * s - n := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r × Fin s)))
        (p := fun u => vA u = true)
      rw [hvA] at h
      have hcard : (Finset.univ : Finset (Fin r × Fin s)).card = r * s := by
        simp [Fintype.card_prod, Fintype.card_fin]
      omega
    have hcompB : (Finset.univ.filter fun u => ¬ vB u = true).card = r * s - n := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r × Fin s)))
        (p := fun u => vB u = true)
      rw [hvB] at h
      have hcard : (Finset.univ : Finset (Fin r × Fin s)).card = r * s := by
        simp [Fintype.card_prod, Fintype.card_fin]
      omega
    have hr1 : P'.rank ≤ r * s - n := by
      calc P'.rank ≤ (Finset.univ.filter fun u => (if vA u then 0 else α) ≠ 0).card :=
            rank_of_sim P' SA _ hSA'
        _ ≤ (Finset.univ.filter fun u => ¬ vA u = true).card := by
            refine Finset.card_le_card fun u hu => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            intro ht; rw [ht] at hu; simp at hu
        _ = r * s - n := hcompA
    have hr2 : (ptr (1 - P')).rank ≤ r * s - n := by
      calc (ptr (1 - P')).rank
          ≤ (Finset.univ.filter fun u =>
              (if vB u then 0 else 1 - α * (1 - lam⁻¹)) ≠ 0).card :=
            rank_of_sim (ptr (1 - P')) SB _ hSB'
        _ ≤ (Finset.univ.filter fun u => ¬ vB u = true).card := by
            refine Finset.card_le_card fun u hu => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            intro ht; rw [ht] at hu; simp at hu
        _ = r * s - n := hcompB
    omega
  have h1 : max r s ≤ 2 * n := twoCut_ge_max hr0 hs0 htc1
  have h2 : max r s ≤ 2 * (r * s - n) := twoCut_ge_max hr0 hs0 htc2
  omega

end MatrixBridge

section ValuationTheorem

private lemma int_prime_of_nat_prime {ℓ : ℕ} (hℓ : Nat.Prime ℓ) : Prime (ℓ : ℤ) := by
  refine ⟨by exact_mod_cast hℓ.ne_zero, ?_, ?_⟩
  · intro hu
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · have : ℓ = 1 := by omega
      exact hℓ.ne_one this
    · omega
  · intro x y hxy
    have hnat : ℓ ∣ (x * y).natAbs := Int.natCast_dvd.mp hxy
    rw [Int.natAbs_mul] at hnat
    rcases hℓ.dvd_mul.mp hnat with hx | hy
    · exact Or.inl (Int.natCast_dvd.mpr hx)
    · exact Or.inr (Int.natCast_dvd.mpr hy)

private lemma prime_dvd_finset_prod {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    {p : R} (hp : Prime p) (s : Finset α) (f : α → R) (h : p ∣ ∏ i ∈ s, f i) :
    ∃ i ∈ s, p ∣ f i := by
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty] at h
      exact (hp.not_unit (isUnit_of_dvd_one h)).elim
  | insert a s ha ih =>
      rw [Finset.prod_insert ha] at h
      rcases hp.dvd_or_dvd h with h1 | h2
      · exact ⟨a, Finset.mem_insert_self a s, h1⟩
      · obtain ⟨i, hi, hid⟩ := ih h2
        exact ⟨i, Finset.mem_insert_of_mem hi, hid⟩

private lemma nat_prime_dvd_finset_prod {α : Type*} [DecidableEq α]
    {p : ℕ} (hp : Nat.Prime p) (s : Finset α) (f : α → ℕ) (h : p ∣ ∏ i ∈ s, f i) :
    ∃ i ∈ s, p ∣ f i := by
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty] at h
      exact (hp.not_dvd_one h).elim
  | insert a s ha ih =>
      rw [Finset.prod_insert ha] at h
      rcases hp.dvd_mul.mp h with h1 | h2
      · exact ⟨a, Finset.mem_insert_self a s, h1⟩
      · obtain ⟨i, hi, hid⟩ := ih h2
        exact ⟨i, Finset.mem_insert_of_mem hi, hid⟩

private lemma sum_prod_partition_one {K : ℕ} (v : Fin K → ℝ) :
    ∑ w : Fin K → Bool, ∏ i : Fin K, (if w i = true then v i else 1 - v i) = 1 := by
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b = true then v i else 1 - v i)]
  refine Finset.prod_eq_one fun i _ => ?_
  simp

/-- **Valuation Theorem (lower bound):**
Let `λ = a / b` in `ℚ` with `p = b / (2a) ∈ [0, 1]`, and let `ℓ` be a prime dividing `a - b`
with `ℓ ∤ a` (hence `ℓ ∤ b`). Then for every `K` and every word-span polynomial `F` with
`ℓ`-integral coefficients `c : (Fin K → Bool) → ℚ` (every 0/1 grouping; every integer combination),
its normalised word-span cost is at least the Bayes error `∑_T min(μ_p(T), μ_{1-p}(T))`. -/
theorem valuation_theorem {K : ℕ} {a b : ℤ} {ℓ : ℕ}
    (hℓ : Nat.Prime ℓ) (hdiv : (ℓ : ℤ) ∣ (a - b)) (hnda : ¬ ((ℓ : ℤ) ∣ a))
    (hb : b ≠ 0) (ha : a ≠ 0)
    (hp0 : 0 ≤ (b : ℝ) / (2 * (a : ℝ))) (hp1 : (b : ℝ) / (2 * (a : ℝ)) ≤ 1)
    (c : (Fin K → Bool) → ℚ) (hc : ∀ w, ¬ (ℓ ∣ (c w).den)) :
    let lam : ℝ := (a : ℝ) / (b : ℝ)
    let p : ℝ := (b : ℝ) / (2 * (a : ℝ))
    let h : (Fin K → Bool) → ℝ := fun T =>
      wordPoly (fun w => (c w : ℝ)) (fun i => if T i then lam else 0)
    (∑ T : Fin K → Bool, min (muP p T) (muP (1 - p) T)) ≤ wordSpanCost p h := by
  intro lam p h
  have hndb : ¬ ((ℓ : ℤ) ∣ b) := by
    intro hdb
    apply hnda
    have : a = (a - b) + b := by ring
    rw [this]
    exact dvd_add hdiv hdb
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hpl : 2 * p * lam = 1 := by
    dsimp only [p, lam]; field_simp [haR, hbR]
  let Dc : ℕ := ∏ w : Fin K → Bool, (c w).den
  have hDc_nd : ¬ (ℓ ∣ Dc) := by
    intro hdivDc
    obtain ⟨w, _, hw⟩ := nat_prime_dvd_finset_prod hℓ Finset.univ (fun w => (c w).den) hdivDc
    exact hc w hw
  let cn : (Fin K → Bool) → ℤ := fun w => (c w).num * ((Dc / (c w).den : ℕ) : ℤ)
  have hcn : ∀ w, (c w : ℚ) * (Dc : ℚ) = (cn w : ℚ) := by
    intro w
    have hdw : (c w).den ∣ Dc := Finset.dvd_prod_of_mem _ (Finset.mem_univ w)
    have hmul : (c w).den * (Dc / (c w).den) = Dc := Nat.mul_div_cancel' hdw
    have hmulQ : ((c w).den : ℚ) * ((Dc / (c w).den : ℕ) : ℚ) = (Dc : ℚ) := by
      exact_mod_cast hmul
    have hnum : (c w : ℚ) * ((c w).den : ℚ) = ((c w).num : ℚ) := Rat.mul_den_eq_num (c w)
    dsimp only [cn]
    push_cast
    calc (c w : ℚ) * (Dc : ℚ)
        = (c w : ℚ) * (((c w).den : ℚ) * ((Dc / (c w).den : ℕ) : ℚ)) := by rw [hmulQ]
      _ = ((c w : ℚ) * ((c w).den : ℚ)) * ((Dc / (c w).den : ℕ) : ℚ) := by ring
      _ = ((c w).num : ℚ) * ((Dc / (c w).den : ℕ) : ℚ) := by rw [hnum]
  have hℓ_int : Prime (ℓ : ℤ) := int_prime_of_nat_prime hℓ
  have hndDc_int : ¬ ((ℓ : ℤ) ∣ (Dc : ℤ)) := by
    intro h1; exact hDc_nd (Int.natCast_dvd_natCast.mp h1)
  have hcore : ∀ T : Fin K → Bool,
      h T ≠ 0 ∨ reflOp p h (fun i => !(T i)) ≠ 1 := by
    intro T
    by_contra hboth
    push Not at hboth
    rcases hboth with ⟨hA0, hB1⟩
    have hA_int : ∑ w : Fin K → Bool, cn w *
        ∏ i : Fin K, (if w i then (if T i then a else 0) else (if T i then b - a else b)) = 0 := by
      have hcast : ((∑ w : Fin K → Bool, cn w *
          ∏ i : Fin K, (if w i then (if T i then a else 0) else (if T i then b - a else b)) : ℤ) : ℝ) = 0 := by
        have hstep : (Dc : ℝ) * (b : ℝ) ^ K * h T =
            ((∑ w : Fin K → Bool, cn w *
              ∏ i : Fin K, (if w i then (if T i then a else 0) else (if T i then b - a else b)) : ℤ) : ℝ) := by
          dsimp only [h, wordPoly]
          rw [Finset.mul_sum]
          push_cast
          refine Finset.sum_congr rfl fun w _ => ?_
          have hcnR : (c w : ℝ) * (Dc : ℝ) = (cn w : ℝ) := by exact_mod_cast hcn w
          have hpow : (b : ℝ) ^ K = ∏ _i : Fin K, (b : ℝ) := by simp
          calc (Dc : ℝ) * (b : ℝ) ^ K *
                ((c w : ℝ) * ∏ i : Fin K, if w i then (if T i then lam else 0) else 1 - (if T i then lam else 0))
              = ((c w : ℝ) * (Dc : ℝ)) *
                ((∏ _i : Fin K, (b : ℝ)) *
                  ∏ i : Fin K, if w i then (if T i then lam else 0) else 1 - (if T i then lam else 0)) := by
                    rw [hpow]; ring
            _ = (cn w : ℝ) *
                ∏ i : Fin K, ((b : ℝ) * if w i then (if T i then lam else 0) else 1 - (if T i then lam else 0)) := by
                    rw [hcnR, ← Finset.prod_mul_distrib]
            _ = (cn w : ℝ) *
                ∏ i : Fin K, (if w i then (if T i then (a : ℝ) else 0) else (if T i then (b : ℝ) - (a : ℝ) else (b : ℝ))) := by
                    congr 1; refine Finset.prod_congr rfl fun i _ => ?_
                    cases w i <;> cases T i <;> dsimp only [lam] <;> simp <;> field_simp [hbR]
        rw [← hstep, hA0, mul_zero]
      exact_mod_cast hcast
    have hA_term_dvd : ∀ w : Fin K → Bool, w ≠ T →
        (ℓ : ℤ) ∣ cn w * ∏ i : Fin K,
          (if w i then (if T i then a else 0) else (if T i then b - a else b)) := by
      intro w hw
      have ⟨i, hi⟩ : ∃ i, w i ≠ T i := by
        by_contra hall; push Not at hall; exact hw (funext hall)
      apply dvd_mul_of_dvd_right
      refine dvd_trans ?_ (Finset.dvd_prod_of_mem
        (fun j => if w j then (if T j then a else 0) else (if T j then b - a else b))
        (Finset.mem_univ i))
      cases hwi : w i <;> cases hTi : T i
      · exact (hi (by rw [hwi, hTi])).elim
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have : b - a = -(a - b) := by ring
        rw [this]; exact dvd_neg.mpr hdiv
      · simp
      · exact (hi (by rw [hwi, hTi])).elim
    have hAT_dvd : (ℓ : ℤ) ∣ cn T * ∏ i : Fin K, (if T i then a else b) := by
      have hsplit : ∑ w : Fin K → Bool, cn w *
          ∏ i : Fin K, (if w i then (if T i then a else 0) else (if T i then b - a else b)) =
          cn T * ∏ i : Fin K, (if T i then a else b) +
          ∑ w ∈ Finset.univ.erase T, cn w *
            ∏ i : Fin K, (if w i then (if T i then a else 0) else (if T i then b - a else b)) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T)]
        congr 2; refine Finset.prod_congr rfl fun i _ => by cases T i <;> simp
      have hrest : (ℓ : ℤ) ∣ ∑ w ∈ Finset.univ.erase T, cn w *
          ∏ i : Fin K, (if w i then (if T i then a else 0) else (if T i then b - a else b)) :=
        Finset.dvd_sum fun w hw => hA_term_dvd w (Finset.ne_of_mem_erase hw)
      rw [hsplit] at hA_int
      have : cn T * ∏ i : Fin K, (if T i then a else b) =
          -(∑ w ∈ Finset.univ.erase T, cn w *
            ∏ i : Fin K, (if w i then (if T i then a else 0) else (if T i then b - a else b))) := by
        linarith
      rw [this]; exact dvd_neg.mpr hrest
    have hcnT_dvd : (ℓ : ℤ) ∣ cn T := by
      rcases hℓ_int.dvd_or_dvd hAT_dvd with h1 | h2
      · exact h1
      · exfalso
        obtain ⟨i, _, hi⟩ := prime_dvd_finset_prod hℓ_int Finset.univ (fun i => if T i then a else b) h2
        cases hTi : T i
        · simp [hTi] at hi; exact hndb hi
        · simp [hTi] at hi; exact hnda hi
    have hB_eq : (1 : ℝ) - reflOp p h (fun i => !(T i)) =
        wordPoly (fun w => (1 : ℝ) - (c w : ℝ)) (fun i => if !(T i) then 1 - lam else 1) := by
      rw [← wordPoly_eval_B hpl (fun w => (c w : ℝ)) (fun i => !(T i))]
      dsimp only [wordPoly]
      have hpart := sum_prod_partition_one (fun i : Fin K => if !(T i) then 1 - lam else 1)
      calc (1 : ℝ) - ∑ w : Fin K → Bool, (c w : ℝ) *
            ∏ i : Fin K, (if w i then (if !(T i) then 1 - lam else 1)
              else 1 - (if !(T i) then 1 - lam else 1))
          = (∑ w : Fin K → Bool,
              ∏ i : Fin K, (if w i then (if !(T i) then 1 - lam else 1)
                else 1 - (if !(T i) then 1 - lam else 1))) -
            ∑ w : Fin K → Bool, (c w : ℝ) *
              ∏ i : Fin K, (if w i then (if !(T i) then 1 - lam else 1)
                else 1 - (if !(T i) then 1 - lam else 1)) := by rw [hpart]
        _ = ∑ w : Fin K → Bool, ((1 : ℝ) - (c w : ℝ)) *
              ∏ i : Fin K, (if w i then (if !(T i) then 1 - lam else 1)
                else 1 - (if !(T i) then 1 - lam else 1)) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun w _ => by ring
    have hB_zero : wordPoly (fun w => (1 : ℝ) - (c w : ℝ))
        (fun i => if !(T i) then 1 - lam else 1) = 0 := by
      rw [← hB_eq, hB1, sub_self]
    have hB_int : ∑ w : Fin K → Bool, ((Dc : ℤ) - cn w) *
        ∏ i : Fin K, (if w i then (if T i then b else b - a) else (if T i then 0 else a)) = 0 := by
      have hcast : ((∑ w : Fin K → Bool, ((Dc : ℤ) - cn w) *
          ∏ i : Fin K, (if w i then (if T i then b else b - a) else (if T i then 0 else a)) : ℤ) : ℝ) = 0 := by
        have hstep : (Dc : ℝ) * (b : ℝ) ^ K *
            wordPoly (fun w => (1 : ℝ) - (c w : ℝ)) (fun i => if !(T i) then 1 - lam else 1) =
            ((∑ w : Fin K → Bool, ((Dc : ℤ) - cn w) *
              ∏ i : Fin K, (if w i then (if T i then b else b - a) else (if T i then 0 else a)) : ℤ) : ℝ) := by
          dsimp only [wordPoly]
          rw [Finset.mul_sum]
          push_cast
          refine Finset.sum_congr rfl fun w _ => ?_
          have hcnR : (c w : ℝ) * (Dc : ℝ) = (cn w : ℝ) := by exact_mod_cast hcn w
          have h1c : ((1 : ℝ) - (c w : ℝ)) * (Dc : ℝ) = (Dc : ℝ) - (cn w : ℝ) := by linarith
          have hpow : (b : ℝ) ^ K = ∏ _i : Fin K, (b : ℝ) := by simp
          calc (Dc : ℝ) * (b : ℝ) ^ K *
                (((1 : ℝ) - (c w : ℝ)) *
                  ∏ i : Fin K, if w i then (if !(T i) then 1 - lam else 1)
                    else 1 - (if !(T i) then 1 - lam else 1))
              = (((1 : ℝ) - (c w : ℝ)) * (Dc : ℝ)) *
                ((∏ _i : Fin K, (b : ℝ)) *
                  ∏ i : Fin K, if w i then (if !(T i) then 1 - lam else 1)
                    else 1 - (if !(T i) then 1 - lam else 1)) := by rw [hpow]; ring
            _ = ((Dc : ℝ) - (cn w : ℝ)) *
                ∏ i : Fin K, ((b : ℝ) * if w i then (if !(T i) then 1 - lam else 1)
                  else 1 - (if !(T i) then 1 - lam else 1)) := by
                    rw [h1c, ← Finset.prod_mul_distrib]
            _ = ((Dc : ℝ) - (cn w : ℝ)) *
                ∏ i : Fin K, (if w i then (if T i then (b : ℝ) else (b : ℝ) - (a : ℝ))
                  else (if T i then 0 else (a : ℝ))) := by
                    congr 1; refine Finset.prod_congr rfl fun i _ => ?_
                    cases w i <;> cases T i <;> dsimp only [lam] <;> simp <;> field_simp [hbR]
        rw [← hstep, hB_zero, mul_zero]
      exact_mod_cast hcast
    have hB_term_dvd : ∀ w : Fin K → Bool, w ≠ T →
        (ℓ : ℤ) ∣ ((Dc : ℤ) - cn w) * ∏ i : Fin K,
          (if w i then (if T i then b else b - a) else (if T i then 0 else a)) := by
      intro w hw
      have ⟨i, hi⟩ : ∃ i, w i ≠ T i := by
        by_contra hall; push Not at hall; exact hw (funext hall)
      apply dvd_mul_of_dvd_right
      refine dvd_trans ?_ (Finset.dvd_prod_of_mem
        (fun j => if w j then (if T j then b else b - a) else (if T j then 0 else a))
        (Finset.mem_univ i))
      cases hwi : w i <;> cases hTi : T i
      · exact (hi (by rw [hwi, hTi])).elim
      · simp
      · simp only [↓reduceIte, Bool.false_eq_true]
        have : b - a = -(a - b) := by ring
        rw [this]; exact dvd_neg.mpr hdiv
      · exact (hi (by rw [hwi, hTi])).elim
    have hBT_dvd : (ℓ : ℤ) ∣ ((Dc : ℤ) - cn T) * ∏ i : Fin K, (if T i then b else a) := by
      have hsplit : ∑ w : Fin K → Bool, ((Dc : ℤ) - cn w) *
          ∏ i : Fin K, (if w i then (if T i then b else b - a) else (if T i then 0 else a)) =
          ((Dc : ℤ) - cn T) * ∏ i : Fin K, (if T i then b else a) +
          ∑ w ∈ Finset.univ.erase T, ((Dc : ℤ) - cn w) *
            ∏ i : Fin K, (if w i then (if T i then b else b - a) else (if T i then 0 else a)) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T)]
        congr 2; refine Finset.prod_congr rfl fun i _ => by cases T i <;> simp
      have hrest : (ℓ : ℤ) ∣ ∑ w ∈ Finset.univ.erase T, ((Dc : ℤ) - cn w) *
          ∏ i : Fin K, (if w i then (if T i then b else b - a) else (if T i then 0 else a)) :=
        Finset.dvd_sum fun w hw => hB_term_dvd w (Finset.ne_of_mem_erase hw)
      rw [hsplit] at hB_int
      have : ((Dc : ℤ) - cn T) * ∏ i : Fin K, (if T i then b else a) =
          -(∑ w ∈ Finset.univ.erase T, ((Dc : ℤ) - cn w) *
            ∏ i : Fin K, (if w i then (if T i then b else b - a) else (if T i then 0 else a))) := by
        linarith
      rw [this]; exact dvd_neg.mpr hrest
    have hDc_sub_dvd : (ℓ : ℤ) ∣ ((Dc : ℤ) - cn T) := by
      rcases hℓ_int.dvd_or_dvd hBT_dvd with h1 | h2
      · exact h1
      · exfalso
        obtain ⟨i, _, hi⟩ := prime_dvd_finset_prod hℓ_int Finset.univ (fun i => if T i then b else a) h2
        cases hTi : T i
        · simp [hTi] at hi; exact hnda hi
        · simp [hTi] at hi; exact hndb hi
    have hDc_dvd : (ℓ : ℤ) ∣ (Dc : ℤ) := by
      have : (Dc : ℤ) = ((Dc : ℤ) - cn T) + cn T := by ring
      rw [this]; exact dvd_add hDc_sub_dvd hcnT_dvd
    exact hndDc_int hDc_dvd
  let flip : (Fin K → Bool) ≃ (Fin K → Bool) :=
    { toFun := fun x i => !(x i)
      invFun := fun x i => !(x i)
      left_inv := fun x => by ext i; simp
      right_inv := fun x => by ext i; simp }
  dsimp only [wordSpanCost]
  rw [← Equiv.sum_comp flip (fun y => if reflOp p h y ≠ 1 then muP p y else 0)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T _ => ?_
  rw [muP_one_sub]
  simp only [flip, Equiv.coe_fn_mk]
  have h1 : 0 ≤ muP p T := muP_nonneg hp0 hp1 T
  have h2 : 0 ≤ muP p (fun i => !(T i)) := muP_nonneg hp0 hp1 (fun i => !(T i))
  rcases hcore T with hA | hB
  · rw [if_pos hA]
    split_ifs <;> linarith [min_le_left (muP p T) (muP p (fun i => !(T i)))]
  · rw [if_pos hB]
    split_ifs <;> linarith [min_le_right (muP p T) (muP p (fun i => !(T i)))]

/-- **Layer grouping upper bound:**
For any `p ∈ (0, 1/2]` and `λ = 1 / (2p)`, the 0/1 layer grouping `c_w = 1` iff `2 * |w| ≥ K`
has cost at most the Bayes error `∑_T min(μ_p(T), μ_{1-p}(T))` at every `K`
(attaining equality whenever the hypotheses of `valuation_theorem` hold). -/
theorem layer_grouping_le {K : ℕ} {p lam : ℝ} (hp0 : 0 < p) (hp12 : p ≤ 1 / 2)
    (hpl : 2 * p * lam = 1) :
    let c : (Fin K → Bool) → ℝ := fun w =>
      if K ≤ 2 * (Finset.univ.filter fun i => w i = true).card then 1 else 0
    let h : (Fin K → Bool) → ℝ := fun T =>
      wordPoly c (fun i => if T i then lam else 0)
    wordSpanCost p h ≤ ∑ T : Fin K → Bool, min (muP p T) (muP (1 - p) T) := by
  intro c h
  have hp1 : p ≤ 1 := by linarith
  have hple : p ≤ 1 - p := by linarith
  have hmu_cmp : ∀ T : Fin K → Bool,
      let wt := (Finset.univ.filter fun i => T i = true).card
      (K ≤ 2 * wt → muP p T ≤ muP (1 - p) T) ∧
      (2 * wt < K → muP (1 - p) T ≤ muP p T) := by
    intro T wt
    have hnot : (Finset.univ.filter fun i => ¬ T i = true).card = K - wt := by
      have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin K)))
        (p := fun i => T i = true)
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hmuT : muP p T = p ^ wt * (1 - p) ^ (K - wt) := by
      simp only [muP, slotWeight]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hnot]
    have hmuF : muP (1 - p) T = (1 - p) ^ wt * p ^ (K - wt) := by
      simp only [muP, slotWeight]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hnot]
      ring
    rw [hmuT, hmuF]
    constructor
    · intro hle
      have hk : K - wt ≤ wt := by omega
      have hpow : p ^ (wt - (K - wt)) ≤ (1 - p) ^ (wt - (K - wt)) :=
        pow_le_pow_left₀ hp0.le hple _
      have hbase : 0 ≤ p ^ (K - wt) * (1 - p) ^ (K - wt) := by positivity
      have hl : p ^ wt * (1 - p) ^ (K - wt) =
          p ^ (wt - (K - wt)) * (p ^ (K - wt) * (1 - p) ^ (K - wt)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
      have hr : (1 - p) ^ (wt - (K - wt)) * (p ^ (K - wt) * (1 - p) ^ (K - wt)) =
          (1 - p) ^ wt * p ^ (K - wt) := by
        have hadd : (1 - p) ^ (wt - (K - wt)) * (1 - p) ^ (K - wt) = (1 - p) ^ wt := by
          rw [← pow_add, Nat.sub_add_cancel hk]
        calc (1 - p) ^ (wt - (K - wt)) * (p ^ (K - wt) * (1 - p) ^ (K - wt))
            = ((1 - p) ^ (wt - (K - wt)) * (1 - p) ^ (K - wt)) * p ^ (K - wt) := by ring
          _ = (1 - p) ^ wt * p ^ (K - wt) := by rw [hadd]
      rw [hl, ← hr]
      exact mul_le_mul_of_nonneg_right hpow hbase
    · intro hlt
      have hk : wt ≤ K - wt := by omega
      have hpow : p ^ ((K - wt) - wt) ≤ (1 - p) ^ ((K - wt) - wt) :=
        pow_le_pow_left₀ hp0.le hple _
      have hbase : 0 ≤ p ^ wt * (1 - p) ^ wt := by positivity
      have hl : (1 - p) ^ wt * p ^ (K - wt) =
          p ^ ((K - wt) - wt) * (p ^ wt * (1 - p) ^ wt) := by
        have hadd : p ^ ((K - wt) - wt) * p ^ wt = p ^ (K - wt) := by
          rw [← pow_add, Nat.sub_add_cancel hk]
        calc (1 - p) ^ wt * p ^ (K - wt)
            = (1 - p) ^ wt * (p ^ ((K - wt) - wt) * p ^ wt) := by rw [hadd]
          _ = p ^ ((K - wt) - wt) * (p ^ wt * (1 - p) ^ wt) := by ring
      have hr : (1 - p) ^ ((K - wt) - wt) * (p ^ wt * (1 - p) ^ wt) =
          p ^ wt * (1 - p) ^ (K - wt) := by
        have hadd : (1 - p) ^ ((K - wt) - wt) * (1 - p) ^ wt = (1 - p) ^ (K - wt) := by
          rw [← pow_add, Nat.sub_add_cancel hk]
        calc (1 - p) ^ ((K - wt) - wt) * (p ^ wt * (1 - p) ^ wt)
            = p ^ wt * ((1 - p) ^ ((K - wt) - wt) * (1 - p) ^ wt) := by ring
          _ = p ^ wt * (1 - p) ^ (K - wt) := by rw [hadd]
      rw [hl, ← hr]
      exact mul_le_mul_of_nonneg_right hpow hbase
  let flip : (Fin K → Bool) ≃ (Fin K → Bool) :=
    { toFun := fun x i => !(x i)
      invFun := fun x i => !(x i)
      left_inv := fun x => by ext i; simp
      right_inv := fun x => by ext i; simp }
  dsimp only [wordSpanCost]
  rw [← Equiv.sum_comp flip (fun y => if reflOp p h y ≠ 1 then muP p y else 0)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T _ => ?_
  rw [muP_one_sub]
  simp only [flip, Equiv.coe_fn_mk]
  by_cases hwt : K ≤ 2 * (Finset.univ.filter fun i => T i = true).card
  · have hB1 : reflOp p h (fun i => !(T i)) = 1 := by
      have hsub : (1 : ℝ) - reflOp p h (fun i => !(T i)) =
          wordPoly (fun w => 1 - c w) (fun i => if !(T i) then 1 - lam else 1) := by
        rw [← wordPoly_eval_B hpl c (fun i => !(T i))]
        dsimp only [wordPoly]
        have hpart := sum_prod_partition_one (fun i : Fin K => if !(T i) then 1 - lam else 1)
        calc (1 : ℝ) - ∑ w : Fin K → Bool, c w *
              ∏ i : Fin K, (if w i then (if !(T i) then 1 - lam else 1)
                else 1 - (if !(T i) then 1 - lam else 1))
            = (∑ w : Fin K → Bool,
                ∏ i : Fin K, (if w i then (if !(T i) then 1 - lam else 1)
                  else 1 - (if !(T i) then 1 - lam else 1))) -
              ∑ w : Fin K → Bool, c w *
                ∏ i : Fin K, (if w i then (if !(T i) then 1 - lam else 1)
                  else 1 - (if !(T i) then 1 - lam else 1)) := by rw [hpart]
          _ = ∑ w : Fin K → Bool, (1 - c w) *
                ∏ i : Fin K, (if w i then (if !(T i) then 1 - lam else 1)
                  else 1 - (if !(T i) then 1 - lam else 1)) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun w _ => by ring
      have hzero : wordPoly (fun w => 1 - c w) (fun i => if !(T i) then 1 - lam else 1) = 0 := by
        refine Finset.sum_eq_zero fun w _ => ?_
        by_cases hsub_w : ∀ i, T i = true → w i = true
        · have hcard : (Finset.univ.filter fun i => T i = true).card ≤
              (Finset.univ.filter fun i => w i = true).card :=
            Finset.card_le_card fun i hi => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
              exact hsub_w i hi
          have hcw : c w = 1 := by
            dsimp only [c]
            exact if_pos (by omega)
          dsimp only
          rw [hcw]; ring
        · push Not at hsub_w
          obtain ⟨i, hTi, hwi⟩ := hsub_w
          have hwf : w i = false := by cases hw : w i <;> simp_all
          have hprod0 : ∏ j : Fin K, (if w j then (if !(T j) then 1 - lam else 1)
              else 1 - (if !(T j) then 1 - lam else 1)) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hTi, hwf])
          dsimp only
          rw [hprod0, mul_zero]
      linarith
    have hmin : muP p T ≤ muP p (fun i => !(T i)) := by
      have := (hmu_cmp T).1 hwt; rwa [muP_one_sub] at this
    rw [hB1, min_eq_left hmin]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, add_zero]
    have hnn : 0 ≤ muP p T := muP_nonneg hp0.le hp1 T
    split_ifs <;> linarith
  · have hA0 : h T = 0 := by
      refine Finset.sum_eq_zero fun w _ => ?_
      by_cases hsub_w : ∀ i, w i = true → T i = true
      · have hcard : (Finset.univ.filter fun i => w i = true).card ≤
            (Finset.univ.filter fun i => T i = true).card :=
          Finset.card_le_card fun i hi => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hsub_w i hi
        have hcw : c w = 0 := by
          dsimp only [c]
          exact if_neg (by omega)
        rw [hcw, zero_mul]
      · push Not at hsub_w
        obtain ⟨i, hwi, hTi⟩ := hsub_w
        have hTf : T i = false := by cases ht : T i <;> simp_all
        have hprod0 : ∏ j : Fin K, (if w j then (if T j then lam else 0)
            else 1 - (if T j then lam else 0)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hwi, hTf])
        rw [hprod0, mul_zero]
    have hmin : muP p (fun i => !(T i)) ≤ muP p T := by
      have := (hmu_cmp T).2 (by omega); rwa [muP_one_sub] at this
    rw [hA0, min_eq_right hmin]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
    have hnn : 0 ≤ muP p (fun i => !(T i)) := muP_nonneg hp0.le hp1 (fun i => !(T i))
    split_ifs <;> linarith

end ValuationTheorem

section CertificatePackings

/-- A Farkas certificate at block length `K` for parameter `p`: a B-grid vector `y` with
nonzero sum `∑ b, y b ≠ 0`. Its A-grid image is `reflOpT p y`. -/
structure ReflCert (p : ℝ) (K : ℕ) where
  y : (Fin K → Bool) → ℝ
  sum_ne : ∑ b : Fin K → Bool, y b ≠ 0

/-- A-grid image of a certificate `c`. -/
def ReflCert.yA {p : ℝ} {K : ℕ} (c : ReflCert p K) : (Fin K → Bool) → ℝ :=
  reflOpT p c.y

/-- Every word-span function `h` must be hit by every certificate `c` either on `supp(yA c)`
(where `h ≠ 0`) or on `supp(c.y)` (where `reflOp p h ≠ 1`). -/
theorem ReflCert.hits {p : ℝ} {K : ℕ} (c : ReflCert p K) (h : (Fin K → Bool) → ℝ) :
    (∃ a, c.yA a ≠ 0 ∧ h a ≠ 0) ∨ (∃ b, c.y b ≠ 0 ∧ reflOp p h b ≠ 1) := by
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨hA, hB⟩
  apply c.sum_ne
  have h1 : ∑ b : Fin K → Bool, c.y b = ∑ b : Fin K → Bool, c.y b * reflOp p h b := by
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hy : c.y b = 0
    · simp [hy]
    · rw [hB b hy, mul_one]
  rw [h1, sum_mul_reflOp]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases hy : c.yA a = 0
  · simp [ReflCert.yA] at hy; rw [hy, zero_mul]
  · rw [hA a hy, mul_zero]

/-- Split `Fin (K₁ + K₂) → Bool` into its prefix and suffix. -/
def splitBits {K₁ K₂ : ℕ} (z : Fin (K₁ + K₂) → Bool) :
    (Fin K₁ → Bool) × (Fin K₂ → Bool) :=
  (fun i => z (Fin.castAdd K₂ i), fun j => z (Fin.natAdd K₁ j))

/-- Equivalence between `Fin (K₁ + K₂) → Bool` and `(Fin K₁ → Bool) × (Fin K₂ → Bool)`. -/
def splitBitsEquiv (K₁ K₂ : ℕ) :
    (Fin (K₁ + K₂) → Bool) ≃ (Fin K₁ → Bool) × (Fin K₂ → Bool) where
  toFun := splitBits
  invFun := fun pq => Fin.append pq.1 pq.2
  left_inv := fun z => by
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro a; simp [splitBits, Fin.append_left]
    · intro b; simp [splitBits, Fin.append_right]
  right_inv := fun ⟨p, q⟩ => by
    ext i
    · simp [splitBits, Fin.append_left]
    · simp [splitBits, Fin.append_right]

theorem muP_split {p : ℝ} {K₁ K₂ : ℕ} (z : Fin (K₁ + K₂) → Bool) :
    muP p z = muP p (splitBits z).1 * muP p (splitBits z).2 := by
  simp only [muP, splitBits, Fin.prod_univ_add]

/-- Tensor product of two certificates. -/
def ReflCert.tensor {p : ℝ} {K₁ K₂ : ℕ} (c₁ : ReflCert p K₁) (c₂ : ReflCert p K₂) :
    ReflCert p (K₁ + K₂) where
  y := fun z => c₁.y (splitBits z).1 * c₂.y (splitBits z).2
  sum_ne := by
    rw [← Equiv.sum_comp (splitBitsEquiv K₁ K₂).symm
      (fun z => c₁.y (splitBits z).1 * c₂.y (splitBits z).2)]
    have heq : ∀ pq : (Fin K₁ → Bool) × (Fin K₂ → Bool),
        c₁.y (splitBits ((splitBitsEquiv K₁ K₂).symm pq)).1 *
          c₂.y (splitBits ((splitBitsEquiv K₁ K₂).symm pq)).2 =
        c₁.y pq.1 * c₂.y pq.2 := by
      intro pq
      have h : splitBits ((splitBitsEquiv K₁ K₂).symm pq) = pq :=
        (splitBitsEquiv K₁ K₂).apply_symm_apply pq
      rw [h]
    simp_rw [heq, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
    exact mul_ne_zero c₁.sum_ne c₂.sum_ne

theorem ReflCert.yA_tensor {p : ℝ} {K₁ K₂ : ℕ} (c₁ : ReflCert p K₁) (c₂ : ReflCert p K₂)
    (a : Fin (K₁ + K₂) → Bool) :
    (c₁.tensor c₂).yA a = c₁.yA (splitBits a).1 * c₂.yA (splitBits a).2 := by
  simp only [ReflCert.yA, reflOpT, ReflCert.tensor]
  rw [← Equiv.sum_comp (splitBitsEquiv K₁ K₂).symm
    (fun b => (∏ i : Fin (K₁ + K₂), reflE p (b i) (a i)) *
      (c₁.y (splitBits b).1 * c₂.y (splitBits b).2))]
  have heq : ∀ pq : (Fin K₁ → Bool) × (Fin K₂ → Bool),
      (∏ i : Fin (K₁ + K₂), reflE p ((splitBitsEquiv K₁ K₂).symm pq i) (a i)) *
        (c₁.y (splitBits ((splitBitsEquiv K₁ K₂).symm pq)).1 *
          c₂.y (splitBits ((splitBitsEquiv K₁ K₂).symm pq)).2) =
      ((∏ i : Fin K₁, reflE p (pq.1 i) ((splitBits a).1 i)) * c₁.y pq.1) *
      ((∏ j : Fin K₂, reflE p (pq.2 j) ((splitBits a).2 j)) * c₂.y pq.2) := by
    intro pq
    have h : splitBits ((splitBitsEquiv K₁ K₂).symm pq) = pq :=
      (splitBitsEquiv K₁ K₂).apply_symm_apply pq
    rw [h, Fin.prod_univ_add]
    have h1 : ∀ i : Fin K₁, (splitBitsEquiv K₁ K₂).symm pq (Fin.castAdd K₂ i) = pq.1 i :=
      fun i => Fin.append_left _ _ i
    have h2 : ∀ j : Fin K₂, (splitBitsEquiv K₁ K₂).symm pq (Fin.natAdd K₁ j) = pq.2 j :=
      fun j => Fin.append_right _ _ j
    simp_rw [h1, h2, splitBits]
    ring
  simp_rw [heq, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]

/-- A fractional packing of Farkas certificates at block length `K` for weight `p`. -/
structure CertPacking (p : ℝ) (K : ℕ) where
  ι : Type
  [fintype : Fintype ι]
  certs : ι → ReflCert p K
  wt : ι → ℝ
  wt_nonneg : ∀ i, 0 ≤ wt i
  loadA_le : ∀ a, ∑ i, (if (certs i).yA a ≠ 0 then wt i else 0) ≤ muP p a
  loadB_le : ∀ b, ∑ i, (if (certs i).y b ≠ 0 then wt i else 0) ≤ muP p b

attribute [instance] CertPacking.fintype

/-- Total value of a certificate packing. -/
def CertPacking.value {p : ℝ} {K : ℕ} (P : CertPacking p K) : ℝ :=
  ∑ i : P.ι, P.wt i

theorem CertPacking.value_nonneg {p : ℝ} {K : ℕ} (P : CertPacking p K) :
    0 ≤ P.value :=
  Finset.sum_nonneg fun i _ => P.wt_nonneg i

/-- **Packing lower bound:** every certificate packing lower-bounds `wordSpanCost`. -/
theorem CertPacking.lower_bound {p : ℝ} {K : ℕ} (P : CertPacking p K)
    (h : (Fin K → Bool) → ℝ) :
    P.value ≤ wordSpanCost p h := by
  have hhit : ∀ i : P.ι,
      P.wt i ≤
        (∑ a : Fin K → Bool, if h a ≠ 0 then (if (P.certs i).yA a ≠ 0 then P.wt i else 0) else 0) +
        (∑ b : Fin K → Bool, if reflOp p h b ≠ 1 then (if (P.certs i).y b ≠ 0 then P.wt i else 0) else 0) := by
    intro i
    have hnnA : ∀ a : Fin K → Bool,
        0 ≤ (if h a ≠ 0 then (if (P.certs i).yA a ≠ 0 then P.wt i else 0) else 0) := by
      intro a; split_ifs <;> linarith [P.wt_nonneg i]
    have hnnB : ∀ b : Fin K → Bool,
        0 ≤ (if reflOp p h b ≠ 1 then (if (P.certs i).y b ≠ 0 then P.wt i else 0) else 0) := by
      intro b; split_ifs <;> linarith [P.wt_nonneg i]
    rcases (P.certs i).hits h with ⟨a, hya, hha⟩ | ⟨b, hyb, hhb⟩
    · have h1 : P.wt i ≤ ∑ x : Fin K → Bool,
          if h x ≠ 0 then (if (P.certs i).yA x ≠ 0 then P.wt i else 0) else 0 := by
        calc P.wt i = (if h a ≠ 0 then (if (P.certs i).yA a ≠ 0 then P.wt i else 0) else 0) := by
              simp [hha, hya]
          _ ≤ _ := Finset.single_le_sum (fun x _ => hnnA x) (Finset.mem_univ a)
      have h2 : 0 ≤ ∑ y : Fin K → Bool,
          if reflOp p h y ≠ 1 then (if (P.certs i).y y ≠ 0 then P.wt i else 0) else 0 :=
        Finset.sum_nonneg fun y _ => hnnB y
      linarith
    · have h1 : 0 ≤ ∑ x : Fin K → Bool,
          if h x ≠ 0 then (if (P.certs i).yA x ≠ 0 then P.wt i else 0) else 0 :=
        Finset.sum_nonneg fun x _ => hnnA x
      have h2 : P.wt i ≤ ∑ y : Fin K → Bool,
          if reflOp p h y ≠ 1 then (if (P.certs i).y y ≠ 0 then P.wt i else 0) else 0 := by
        calc P.wt i = (if reflOp p h b ≠ 1 then (if (P.certs i).y b ≠ 0 then P.wt i else 0) else 0) := by
              simp [hhb, hyb]
          _ ≤ _ := Finset.single_le_sum (fun y _ => hnnB y) (Finset.mem_univ b)
      linarith
  have hcomm1 : (∑ i : P.ι, ∑ a : Fin K → Bool,
        if h a ≠ 0 then (if (P.certs i).yA a ≠ 0 then P.wt i else 0) else 0) =
      ∑ a : Fin K → Bool, ∑ i : P.ι,
        if h a ≠ 0 then (if (P.certs i).yA a ≠ 0 then P.wt i else 0) else 0 :=
    Finset.sum_comm
  have hcomm2 : (∑ i : P.ι, ∑ b : Fin K → Bool,
        if reflOp p h b ≠ 1 then (if (P.certs i).y b ≠ 0 then P.wt i else 0) else 0) =
      ∑ b : Fin K → Bool, ∑ i : P.ι,
        if reflOp p h b ≠ 1 then (if (P.certs i).y b ≠ 0 then P.wt i else 0) else 0 :=
    Finset.sum_comm
  calc P.value
      ≤ ∑ i : P.ι,
          ((∑ a : Fin K → Bool, if h a ≠ 0 then (if (P.certs i).yA a ≠ 0 then P.wt i else 0) else 0) +
           (∑ b : Fin K → Bool, if reflOp p h b ≠ 1 then (if (P.certs i).y b ≠ 0 then P.wt i else 0) else 0)) :=
        Finset.sum_le_sum fun i _ => hhit i
    _ = (∑ a : Fin K → Bool, ∑ i : P.ι, if h a ≠ 0 then (if (P.certs i).yA a ≠ 0 then P.wt i else 0) else 0) +
        (∑ b : Fin K → Bool, ∑ i : P.ι, if reflOp p h b ≠ 1 then (if (P.certs i).y b ≠ 0 then P.wt i else 0) else 0) := by
        rw [Finset.sum_add_distrib, hcomm1, hcomm2]
    _ ≤ wordSpanCost p h := by
        dsimp only [wordSpanCost]
        apply add_le_add
        · refine Finset.sum_le_sum fun a _ => ?_
          by_cases hha : h a = 0
          · simp [hha]
          · simp only [hha, ne_eq, not_false_eq_true, ↓reduceIte]; exact P.loadA_le a
        · refine Finset.sum_le_sum fun b _ => ?_
          by_cases hhb : reflOp p h b = 1
          · simp [hhb]
          · simp only [hhb, ne_eq, not_false_eq_true, ↓reduceIte]; exact P.loadB_le b

/-- **Tensorisation of packings:** values multiply across block lengths. -/
def CertPacking.tensor {p : ℝ} {K₁ K₂ : ℕ}
    (P₁ : CertPacking p K₁) (P₂ : CertPacking p K₂) :
    CertPacking p (K₁ + K₂) where
  ι := P₁.ι × P₂.ι
  certs := fun ij => (P₁.certs ij.1).tensor (P₂.certs ij.2)
  wt := fun ij => P₁.wt ij.1 * P₂.wt ij.2
  wt_nonneg := fun ij => mul_nonneg (P₁.wt_nonneg ij.1) (P₂.wt_nonneg ij.2)
  loadA_le := fun a => by
    rw [muP_split]
    have hsplit : ∑ ij : P₁.ι × P₂.ι,
        (if ((P₁.certs ij.1).tensor (P₂.certs ij.2)).yA a ≠ 0 then P₁.wt ij.1 * P₂.wt ij.2 else 0) =
        (∑ i : P₁.ι, if (P₁.certs i).yA (splitBits a).1 ≠ 0 then P₁.wt i else 0) *
        (∑ j : P₂.ι, if (P₂.certs j).yA (splitBits a).2 ≠ 0 then P₂.wt j else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ReflCert.yA_tensor]
      by_cases h1 : (P₁.certs i).yA (splitBits a).1 = 0 <;>
        by_cases h2 : (P₂.certs j).yA (splitBits a).2 = 0 <;>
        simp [h1, h2]
    rw [hsplit]
    have hnn1 : 0 ≤ ∑ i : P₁.ι, if (P₁.certs i).yA (splitBits a).1 ≠ 0 then P₁.wt i else 0 :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> linarith [P₁.wt_nonneg i]
    have hnn2 : 0 ≤ ∑ j : P₂.ι, if (P₂.certs j).yA (splitBits a).2 ≠ 0 then P₂.wt j else 0 :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> linarith [P₂.wt_nonneg j]
    have hmu1 : 0 ≤ muP p (splitBits a).1 := le_trans hnn1 (P₁.loadA_le _)
    exact mul_le_mul (P₁.loadA_le _) (P₂.loadA_le _) hnn2 hmu1
  loadB_le := fun b => by
    rw [muP_split]
    have hsplit : ∑ ij : P₁.ι × P₂.ι,
        (if ((P₁.certs ij.1).tensor (P₂.certs ij.2)).y b ≠ 0 then P₁.wt ij.1 * P₂.wt ij.2 else 0) =
        (∑ i : P₁.ι, if (P₁.certs i).y (splitBits b).1 ≠ 0 then P₁.wt i else 0) *
        (∑ j : P₂.ι, if (P₂.certs j).y (splitBits b).2 ≠ 0 then P₂.wt j else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [ReflCert.tensor]
      by_cases h1 : (P₁.certs i).y (splitBits b).1 = 0 <;>
        by_cases h2 : (P₂.certs j).y (splitBits b).2 = 0 <;>
        simp [h1, h2]
    rw [hsplit]
    have hnn1 : 0 ≤ ∑ i : P₁.ι, if (P₁.certs i).y (splitBits b).1 ≠ 0 then P₁.wt i else 0 :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> linarith [P₁.wt_nonneg i]
    have hnn2 : 0 ≤ ∑ j : P₂.ι, if (P₂.certs j).y (splitBits b).2 ≠ 0 then P₂.wt j else 0 :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> linarith [P₂.wt_nonneg j]
    have hmu1 : 0 ≤ muP p (splitBits b).1 := le_trans hnn1 (P₁.loadB_le _)
    exact mul_le_mul (P₁.loadB_le _) (P₂.loadB_le _) hnn2 hmu1

theorem CertPacking.value_tensor {p : ℝ} {K₁ K₂ : ℕ}
    (P₁ : CertPacking p K₁) (P₂ : CertPacking p K₂) :
    (P₁.tensor P₂).value = P₁.value * P₂.value := by
  dsimp only [CertPacking.value, CertPacking.tensor]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- Trivial `K = 0` packing of value `1`. -/
def CertPacking.unit (p : ℝ) : CertPacking p 0 where
  ι := Unit
  certs := fun _ =>
    { y := fun _ => 1
      sum_ne := by simp }
  wt := fun _ => 1
  wt_nonneg := fun _ => by norm_num
  loadA_le := fun _ => by
    simp only [Finset.univ_unique, Finset.sum_singleton, muP, Finset.univ_eq_empty, Finset.prod_empty]
    split_ifs <;> norm_num
  loadB_le := fun _ => by
    simp only [Finset.univ_unique, Finset.sum_singleton, muP, Finset.univ_eq_empty, Finset.prod_empty]
    split_ifs <;> norm_num

theorem CertPacking.value_unit (p : ℝ) : (CertPacking.unit p).value = 1 := by
  simp [CertPacking.value, CertPacking.unit]

/-- Reindex a packing along an equality of block lengths. -/
def CertPacking.cast {p : ℝ} {K₁ K₂ : ℕ} (hK : K₁ = K₂) (P : CertPacking p K₁) :
    CertPacking p K₂ :=
  hK ▸ P

theorem CertPacking.value_cast {p : ℝ} {K₁ K₂ : ℕ} (hK : K₁ = K₂) (P : CertPacking p K₁) :
    (P.cast hK).value = P.value := by
  subst hK; rfl

/-- Tensor power `P^{⊗m}` of a block-`B` packing, at block length `m * B`. -/
def CertPacking.pow {p : ℝ} {B : ℕ} (P : CertPacking p B) :
    (m : ℕ) → CertPacking p (m * B)
  | 0 => (CertPacking.unit p).cast (by simp)
  | m + 1 => ((P.pow m).tensor P).cast (by ring)

theorem CertPacking.value_pow {p : ℝ} {B : ℕ} (P : CertPacking p B) :
    ∀ m : ℕ, (P.pow m).value = P.value ^ m
  | 0 => by simp [CertPacking.pow, CertPacking.value_cast, CertPacking.value_unit]
  | m + 1 => by
      simp [CertPacking.pow, CertPacking.value_cast, CertPacking.value_tensor,
        CertPacking.value_pow P m, pow_succ]

/-- Any positive block-`B` packing `P` together with a positive `K = 1` packing `P₁` gives an
asymptotic lower bound `c * g ^ K ≤ wordSpanCost p h` for every `K` and `h`, where
`g = P.value ^ (1 / B)`. -/
theorem CertPacking.asymptotic_bound {p : ℝ} {B : ℕ} (hB : 0 < B)
    (P : CertPacking p B) (hP : 0 < P.value)
    (P₁ : CertPacking p 1) (hP₁ : 0 < P₁.value) :
    ∃ c > 0, ∀ (K : ℕ) (h : (Fin K → Bool) → ℝ),
      c * (P.value ^ ((1 : ℝ) / (B : ℝ))) ^ K ≤ wordSpanCost p h := by
  set g : ℝ := P.value ^ ((1 : ℝ) / (B : ℝ)) with hg
  have hg_pos : 0 < g := Real.rpow_pos_of_pos hP _
  have hgB : g ^ B = P.value := by
    rw [hg, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
    have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    rw [show ((1 : ℝ) / (B : ℝ)) * (B : ℝ) = 1 by field_simp [hBne], Real.rpow_one]
  let q : ℝ := P₁.value / g
  have hq_pos : 0 < q := div_pos hP₁ hg_pos
  refine ⟨min 1 (q ^ B), lt_min one_pos (pow_pos hq_pos B), fun K h => ?_⟩
  let m := K / B
  let r := K % B
  have hKr : m * B + r = K := by
    have := Nat.div_add_mod K B; rw [mul_comm] at this; exact this
  have hrB : r < B := Nat.mod_lt K hB
  let PK : CertPacking p K := ((P.pow m).tensor ((P₁.pow r).cast (by simp))).cast hKr
  have hPK_val : PK.value = P.value ^ m * P₁.value ^ r := by
    simp [PK, CertPacking.value_cast, CertPacking.value_tensor, CertPacking.value_pow]
  have hbound : PK.value ≤ wordSpanCost p h := PK.lower_bound h
  have hmin_le : min 1 (q ^ B) ≤ q ^ r := by
    rcases le_or_gt 1 q with hq1 | hq1
    · exact le_trans (min_le_left _ _) (one_le_pow₀ hq1)
    · have : q ^ B ≤ q ^ r := pow_le_pow_of_le_one hq_pos.le hq1.le hrB.le
      exact le_trans (min_le_right _ _) this
  have hgK : g ^ K = P.value ^ m * g ^ r := by
    rw [← hKr, pow_add, mul_comm m B, pow_mul, hgB]
  have hmain : min 1 (q ^ B) * g ^ K ≤ P.value ^ m * P₁.value ^ r := by
    rw [hgK]
    have hqr : q ^ r * g ^ r = P₁.value ^ r := by
      rw [← mul_pow]; dsimp only [q]; rw [div_mul_cancel₀ _ hg_pos.ne']
    calc min 1 (q ^ B) * (P.value ^ m * g ^ r)
        = P.value ^ m * (min 1 (q ^ B) * g ^ r) := by ring
      _ ≤ P.value ^ m * (q ^ r * g ^ r) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hmin_le (pow_nonneg hg_pos.le r)
          · exact pow_nonneg hP.le m
      _ = P.value ^ m * P₁.value ^ r := by rw [hqr]
  linarith

end CertificatePackings

section ExplicitPackings

/-- Helper `K = 1` certificate `a = δ_false`. -/
def certA (p : ℝ) : ReflCert p 1 where
  y := fun b => if b 0 then 0 else 1
  sum_ne := by
    have h : ∑ b : Fin 1 → Bool, (if b 0 then (0 : ℝ) else 1) = 1 := by
      let e : (Fin 1 → Bool) ≃ Bool := Equiv.funUnique (Fin 1) Bool
      rw [← Equiv.sum_comp e.symm (fun b => if b 0 then (0 : ℝ) else 1)]
      simp [e]
    rw [h]; norm_num

/-- Helper `K = 1` certificate `b = δ_true`. -/
def certB (p : ℝ) : ReflCert p 1 where
  y := fun b => if b 0 then 1 else 0
  sum_ne := by
    have h : ∑ b : Fin 1 → Bool, (if b 0 then (1 : ℝ) else 0) = 1 := by
      let e : (Fin 1 → Bool) ≃ Bool := Equiv.funUnique (Fin 1) Bool
      rw [← Equiv.sum_comp e.symm (fun b => if b 0 then (1 : ℝ) else 0)]
      simp [e]
    rw [h]; norm_num

/-- Helper `K = 1` certificate `c = (2 - 2p, 2p - 1)` with `yA(c) = (0, 1)`. -/
def certC (p : ℝ) : ReflCert p 1 where
  y := fun b => if b 0 then 2 * p - 1 else 2 - 2 * p
  sum_ne := by
    have h : ∑ b : Fin 1 → Bool, (if b 0 then 2 * p - 1 else 2 - 2 * p) = 1 := by
      let e : (Fin 1 → Bool) ≃ Bool := Equiv.funUnique (Fin 1) Bool
      rw [← Equiv.sum_comp e.symm (fun b => if b 0 then 2 * p - 1 else 2 - 2 * p)]
      simp [e]; ring
    rw [h]; norm_num

/-- Helper `K = 1` certificate `d = (1 - 2p, 2p)` with `yA(d) = (1, 0)`. -/
def certD (p : ℝ) : ReflCert p 1 where
  y := fun b => if b 0 then 2 * p else 1 - 2 * p
  sum_ne := by
    have h : ∑ b : Fin 1 → Bool, (if b 0 then 2 * p else 1 - 2 * p) = 1 := by
      let e : (Fin 1 → Bool) ≃ Bool := Equiv.funUnique (Fin 1) Bool
      rw [← Equiv.sum_comp e.symm (fun b => if b 0 then 2 * p else 1 - 2 * p)]
      simp [e]
    rw [h]; norm_num

private lemma certC_yA (p : ℝ) (a : Fin 1 → Bool) :
    (certC p).yA a = if a 0 then 1 else 0 := by
  dsimp only [ReflCert.yA, reflOpT, certC]
  let e : (Fin 1 → Bool) ≃ Bool := Equiv.funUnique (Fin 1) Bool
  rw [← Equiv.sum_comp e.symm
    (fun b => (∏ i : Fin 1, reflE p (b i) (a i)) * if b 0 then 2 * p - 1 else 2 - 2 * p)]
  cases ha : a 0 <;> simp [e, reflE, ha] <;> ring

private lemma certD_yA (p : ℝ) (a : Fin 1 → Bool) :
    (certD p).yA a = if a 0 then 0 else 1 := by
  dsimp only [ReflCert.yA, reflOpT, certD]
  let e : (Fin 1 → Bool) ≃ Bool := Equiv.funUnique (Fin 1) Bool
  rw [← Equiv.sum_comp e.symm
    (fun b => (∏ i : Fin 1, reflE p (b i) (a i)) * if b 0 then 2 * p else 1 - 2 * p)]
  cases ha : a 0 <;> simp [e, reflE, ha] <;> ring

/-- Trivial `K = 1` packing of value `min p (1 - p) > 0` for any `p ∈ (0, 1)`. -/
def packing_K1_trivial {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : CertPacking p 1 where
  ι := Unit
  certs := fun _ => certA p
  wt := fun _ => min p (1 - p)
  wt_nonneg := fun _ => le_min hp0.le (by linarith)
  loadA_le := fun a => by
    rw [Finset.univ_unique, Finset.sum_singleton, muP, Fin.prod_univ_one]
    simp only [slotWeight]
    cases ha : a 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · exact min_le_right _ _
      · linarith
    · simp only [↓reduceIte]
      split_ifs
      · exact min_le_left _ _
      · linarith
  loadB_le := fun b => by
    rw [Finset.univ_unique, Finset.sum_singleton, muP, Fin.prod_univ_one]
    simp only [slotWeight, certA]
    by_cases hb : b 0 = true
    · simp [hb, hp0.le]
    · simp [hb]

theorem packing_K1_trivial_value {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (packing_K1_trivial hp0 hp1).value = min p (1 - p) := by
  simp [CertPacking.value, packing_K1_trivial]

/-- Parametric `K = 1` packing of value `2/3` on `p ∈ [1/3, 2/3]`. -/
noncomputable def packing_K1_mid {p : ℝ} (h1 : 1 / 3 ≤ p) (h2 : p ≤ 2 / 3) : CertPacking p 1 where
  ι := Fin 4
  certs := fun i => match i with
    | ⟨0, _⟩ => certA p
    | ⟨1, _⟩ => certB p
    | ⟨2, _⟩ => certC p
    | ⟨3, _⟩ => certD p
  wt := fun i => match i with
    | ⟨0, _⟩ => 2 / 3 - p
    | ⟨1, _⟩ => p - 1 / 3
    | ⟨2, _⟩ => p - 1 / 3
    | ⟨3, _⟩ => 2 / 3 - p
  wt_nonneg := fun i => by fin_cases i <;> dsimp <;> linarith
  loadA_le := fun a => by
    simp only [Fin.sum_univ_four, muP, Fin.prod_univ_one, slotWeight, certC_yA, certD_yA]
    have hw0 : 0 ≤ 2 / 3 - p := by linarith
    have hw1 : 0 ≤ p - 1 / 3 := by linarith
    cases ha : a 0
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false, one_ne_zero,
        not_false_eq_true]
      have h0 : (if (certA p).yA a ≠ 0 then 2 / 3 - p else 0) ≤ 2 / 3 - p := by split_ifs <;> linarith
      have h1' : (if (certB p).yA a ≠ 0 then p - 1 / 3 else 0) ≤ p - 1 / 3 := by split_ifs <;> linarith
      linarith
    · simp only [↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]
      have h0 : (if (certA p).yA a ≠ 0 then 2 / 3 - p else 0) ≤ 2 / 3 - p := by split_ifs <;> linarith
      have h1' : (if (certB p).yA a ≠ 0 then p - 1 / 3 else 0) ≤ p - 1 / 3 := by split_ifs <;> linarith
      linarith
  loadB_le := fun b => by
    simp only [Fin.sum_univ_four, muP, Fin.prod_univ_one, slotWeight, certA, certB, certC, certD]
    have hw0 : 0 ≤ 2 / 3 - p := by linarith
    have hw1 : 0 ≤ p - 1 / 3 := by linarith
    cases hb : b 0
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true,
        not_true_eq_false]
      have h2' : (if 2 - 2 * p ≠ 0 then p - 1 / 3 else 0) ≤ p - 1 / 3 := by split_ifs <;> linarith
      have h3' : (if 1 - 2 * p ≠ 0 then 2 / 3 - p else 0) ≤ 2 / 3 - p := by split_ifs <;> linarith
      linarith
    · simp only [↓reduceIte, ne_eq, not_true_eq_false, one_ne_zero, not_false_eq_true]
      have h2' : (if 2 * p - 1 ≠ 0 then p - 1 / 3 else 0) ≤ p - 1 / 3 := by split_ifs <;> linarith
      have h3' : (if 2 * p ≠ 0 then 2 / 3 - p else 0) ≤ 2 / 3 - p := by split_ifs <;> linarith
      linarith

theorem packing_K1_mid_value {p : ℝ} (h1 : 1 / 3 ≤ p) (h2 : p ≤ 2 / 3) :
    (packing_K1_mid h1 h2).value = 2 / 3 := by
  change (∑ i : Fin 4, match i with
    | ⟨0, _⟩ => 2 / 3 - p
    | ⟨1, _⟩ => p - 1 / 3
    | ⟨2, _⟩ => p - 1 / 3
    | ⟨3, _⟩ => 2 / 3 - p) = 2 / 3
  rw [Fin.sum_univ_four]
  dsimp only
  ring

/-- The `K = 2` eigenvector certificate `C3 = (1 - p) δ_{00} + p δ_{11}`. -/
def certC3 (p : ℝ) : ReflCert p 2 where
  y := fun b =>
    match b 0, b 1 with
    | false, false => 1 - p
    | true, true => p
    | _, _ => 0
  sum_ne := by
    let f : (Fin 2 → Bool) → ℝ := fun b =>
      match b 0, b 1 with | false, false => 1 - p | true, true => p | _, _ => 0
    have h : ∑ b : Fin 2 → Bool, f b = 1 := by
      let e : (Fin 2 → Bool) ≃ Bool × Bool :=
        { toFun := fun f => (f 0, f 1)
          invFun := fun pq i => if i = 0 then pq.1 else pq.2
          left_inv := fun f => by ext i; fin_cases i <;> rfl
          right_inv := fun ⟨_, _⟩ => rfl }
      rw [← Equiv.sum_comp e.symm f]
      simp [f, e, Fintype.sum_prod_type]
    change ∑ b : Fin 2 → Bool, f b ≠ 0
    rw [h]; norm_num

private lemma certC3_yA (p : ℝ) (a : Fin 2 → Bool) :
    (certC3 p).yA a = match a 0, a 1 with
      | false, false => 1 - p
      | true, true => p
      | _, _ => 0 := by
  dsimp only [ReflCert.yA, reflOpT, certC3]
  let e : (Fin 2 → Bool) ≃ Bool × Bool :=
    { toFun := fun f => (f 0, f 1)
      invFun := fun pq i => if i = 0 then pq.1 else pq.2
      left_inv := fun f => by ext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [← Equiv.sum_comp e.symm (fun b =>
    (∏ i : Fin 2, reflE p (b i) (a i)) *
      match b 0, b 1 with | false, false => 1 - p | true, true => p | _, _ => 0)]
  cases ha0 : a 0 <;> cases ha1 : a 1 <;>
    simp [e, Fintype.sum_prod_type, Fin.prod_univ_two, reflE, ha0, ha1] <;> ring

/-- Parametric `K = 2` packing of value `min (2p - p²) ((1 - p)²)` on `p ∈ (0, 1/2]`. -/
noncomputable def packing_K2 {p : ℝ} (hp0 : 0 < p) (hp12 : p ≤ 1 / 2) : CertPacking p 2 :=
  let α : ℝ := min 1 ((1 - p) ^ 2 / (2 * p - p ^ 2))
  have hden_pos : 0 < 2 * p - p ^ 2 := by nlinarith
  have hα_nonneg : 0 ≤ α := le_min zero_le_one (div_nonneg (sq_nonneg _) hden_pos.le)
  have hα_le_one : α ≤ 1 := min_le_left _ _
  have hα_mul : α * (2 * p - p ^ 2) ≤ (1 - p) ^ 2 := by
    calc α * (2 * p - p ^ 2)
        ≤ ((1 - p) ^ 2 / (2 * p - p ^ 2)) * (2 * p - p ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hden_pos.le
      _ = (1 - p) ^ 2 := div_mul_cancel₀ _ hden_pos.ne'
  { ι := Fin 3
    certs := fun i => match i with
      | ⟨0, _⟩ => (certD p).tensor (certA p)
      | ⟨1, _⟩ => (certA p).tensor (certD p)
      | ⟨2, _⟩ => certC3 p
    wt := fun i => match i with
      | ⟨0, _⟩ => α * (p * (1 - p))
      | ⟨1, _⟩ => α * (p * (1 - p))
      | ⟨2, _⟩ => α * p ^ 2
    wt_nonneg := fun i => by
      fin_cases i <;> dsimp
      · exact mul_nonneg hα_nonneg (mul_nonneg hp0.le (by linarith))
      · exact mul_nonneg hα_nonneg (mul_nonneg hp0.le (by linarith))
      · exact mul_nonneg hα_nonneg (sq_nonneg _)
    loadA_le := fun a => by
      simp only [Fin.sum_univ_three, ReflCert.yA_tensor, certD_yA, certC3_yA, muP,
        Fin.prod_univ_two, slotWeight, splitBits]
      have h00 : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin 2) := rfl
      have h01 : Fin.natAdd 1 (0 : Fin 1) = (1 : Fin 2) := rfl
      simp only [h00, h01]
      have hp1m : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
      have hw1 : 0 ≤ α * (p * (1 - p)) := mul_nonneg hα_nonneg hp1m
      have hw1_le : α * (p * (1 - p)) ≤ p * (1 - p) := by nlinarith
      have hw2 : 0 ≤ α * p ^ 2 := mul_nonneg hα_nonneg (sq_nonneg _)
      have hw2_le : α * p ^ 2 ≤ p ^ 2 := by nlinarith [sq_nonneg p]
      cases ha0 : a 0 <;> cases ha1 : a 1
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, ne_eq]
        have t0 : (if (certA p).yA (fun j => a (Fin.natAdd 1 j)) ≠ 0 then α * (p * (1 - p)) else 0) ≤
            α * (p * (1 - p)) := by split_ifs <;> linarith
        have t1 : (if (certA p).yA (fun i => a (Fin.castAdd 1 i)) ≠ 0 then α * (p * (1 - p)) else 0) ≤
            α * (p * (1 - p)) := by split_ifs <;> linarith
        have t2 : (if (1 - p : ℝ) ≠ 0 then α * p ^ 2 else 0) ≤ α * p ^ 2 := by
          split_ifs <;> linarith
        have : α * (p * (1 - p)) + α * (p * (1 - p)) + α * p ^ 2 = α * (2 * p - p ^ 2) := by ring
        nlinarith
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_zero, ne_eq, not_true_eq_false]
        have t0 : (if (certA p).yA (fun j => a (Fin.natAdd 1 j)) ≠ 0 then α * (p * (1 - p)) else 0) ≤
            α * (p * (1 - p)) := by split_ifs <;> linarith
        nlinarith
      · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, mul_one, ne_eq, not_true_eq_false]
        have t1 : (if (certA p).yA (fun i => a (Fin.castAdd 1 i)) ≠ 0 then α * (p * (1 - p)) else 0) ≤
            α * (p * (1 - p)) := by split_ifs <;> linarith
        nlinarith
      · simp only [↓reduceIte, zero_mul, mul_zero, ne_eq, not_true_eq_false]
        have t2 : (if p ≠ 0 then α * p ^ 2 else 0) ≤ α * p ^ 2 := by split_ifs <;> linarith
        nlinarith
    loadB_le := fun b => by
      simp only [Fin.sum_univ_three, ReflCert.tensor, certD, certA, certC3, muP,
        Fin.prod_univ_two, slotWeight, splitBits]
      have h00 : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin 2) := rfl
      have h01 : Fin.natAdd 1 (0 : Fin 1) = (1 : Fin 2) := rfl
      simp only [h00, h01]
      have hp1m : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
      have hw1 : 0 ≤ α * (p * (1 - p)) := mul_nonneg hα_nonneg hp1m
      have hw1_le : α * (p * (1 - p)) ≤ p * (1 - p) := by nlinarith
      have hw2 : 0 ≤ α * p ^ 2 := mul_nonneg hα_nonneg (sq_nonneg _)
      have hw2_le : α * p ^ 2 ≤ p ^ 2 := by nlinarith [sq_nonneg p]
      cases hb0 : b 0 <;> cases hb1 : b 1
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, ne_eq]
        have t0 : (if 1 - 2 * p ≠ 0 then α * (p * (1 - p)) else 0) ≤ α * (p * (1 - p)) := by
          split_ifs <;> linarith
        have t2 : (if (1 - p : ℝ) ≠ 0 then α * p ^ 2 else 0) ≤ α * p ^ 2 := by
          split_ifs <;> linarith
        have : α * (p * (1 - p)) + α * (p * (1 - p)) + α * p ^ 2 = α * (2 * p - p ^ 2) := by ring
        nlinarith
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_zero, ne_eq, not_true_eq_false]
        have t1 : (if 2 * p ≠ 0 then α * (p * (1 - p)) else 0) ≤ α * (p * (1 - p)) := by
          split_ifs <;> linarith
        nlinarith
      · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, mul_one, ne_eq, not_true_eq_false]
        have t0 : (if 2 * p ≠ 0 then α * (p * (1 - p)) else 0) ≤ α * (p * (1 - p)) := by
          split_ifs <;> linarith
        nlinarith
      · simp only [↓reduceIte, zero_mul, mul_zero, ne_eq, not_true_eq_false]
        have t2 : (if p ≠ 0 then α * p ^ 2 else 0) ≤ α * p ^ 2 := by split_ifs <;> linarith
        nlinarith }

theorem packing_K2_value {p : ℝ} (hp0 : 0 < p) (hp12 : p ≤ 1 / 2) :
    (packing_K2 hp0 hp12).value = min (2 * p - p ^ 2) ((1 - p) ^ 2) := by
  have hden_pos : 0 < 2 * p - p ^ 2 := by nlinarith
  let α : ℝ := min 1 ((1 - p) ^ 2 / (2 * p - p ^ 2))
  change (∑ i : Fin 3, match i with
    | ⟨0, _⟩ => α * (p * (1 - p))
    | ⟨1, _⟩ => α * (p * (1 - p))
    | ⟨2, _⟩ => α * p ^ 2) = min (2 * p - p ^ 2) ((1 - p) ^ 2)
  rw [Fin.sum_univ_three]
  dsimp only
  have h1 : α * (p * (1 - p)) + α * (p * (1 - p)) + α * p ^ 2 = α * (2 * p - p ^ 2) := by ring
  rw [h1]
  dsimp only [α]
  rw [min_mul_of_nonneg _ _ hden_pos.le, one_mul, div_mul_cancel₀ _ hden_pos.ne']

/-! ### Exact 22-certificate `K = 4, p = 1/4` rational packing (value `57/256`) -/

private def bits4ToFin16 (x : Fin 4 → Bool) : Fin 16 :=
  ⟨(if x 0 then 1 else 0) + 2 * (if x 1 then 1 else 0) +
   4 * (if x 2 then 1 else 0) + 8 * (if x 3 then 1 else 0), by
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide⟩

private def fin16ToBits4 (k : Fin 16) : Fin 4 → Bool :=
  fun i => (k.val / 2 ^ i.val) % 2 == 1

private def bits4Equiv : (Fin 4 → Bool) ≃ Fin 16 where
  toFun := bits4ToFin16
  invFun := fin16ToBits4
  left_inv := fun x => by
    ext i
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      fin_cases i <;> simp [fin16ToBits4, bits4ToFin16, h0, h1, h2, h3]
  right_inv := fun k => by
    fin_cases k <;> decide

private def e2Int (b a : Bool) : ℤ :=
  match b, a with
  | false, false => 1
  | false, true => 1
  | true, false => 3
  | true, true => -1

private lemma e2Int_eq (b a : Bool) :
    ((e2Int b a : ℤ) : ℝ) / 2 = reflE (1 / 4 : ℝ) b a := by
  cases b <;> cases a <;> simp [e2Int, reflE] <;> norm_num

private def e2Tensor4 (b a : Fin 16) : ℤ :=
  let fb := fin16ToBits4 b
  let fa := fin16ToBits4 a
  e2Int (fb 0) (fa 0) * e2Int (fb 1) (fa 1) * e2Int (fb 2) (fa 2) * e2Int (fb 3) (fa 3)

private lemma e2Tensor4_eq (b a : Fin 16) :
    ((e2Tensor4 b a : ℤ) : ℝ) / 16 =
    ∏ i : Fin 4, reflE (1 / 4 : ℝ) (fin16ToBits4 b i) (fin16ToBits4 a i) := by
  simp only [e2Tensor4, Fin.prod_univ_four, ← e2Int_eq]
  push_cast
  ring

private def certPi4 (c : Fin 22) : ℕ :=
  match c.val with
  | 0 => 58 | 1 => 72 | 2 => 58 | 3 => 58 | 4 => 72
  | 5 => 14 | 6 => 58 | 7 => 2 | 8 => 14 | 9 => 2
  | 10 => 3 | 11 => 14 | 12 => 14 | 13 => 3 | 14 => 2
  | 15 => 2 | 16 => 2 | 17 => 2 | 18 => 2 | 19 => 2
  | 20 => 1 | _ => 1

private def certY4Row (c : Fin 22) : List ℤ :=
  match c.val with
  | 0 => [6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => [6, 6, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [6, 0, 6, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => [6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0]
  | 4 => [6, 0, 6, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0]
  | 5 => [9, 0, 0, 3, 9, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]
  | 6 => [6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0]
  | 7 => [-36, 0, 18, 0, 18, 0, 0, 0, 18, 0, 0, 0, 0, 0, 6, 0]
  | 8 => [9, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0]
  | 9 => [12, -3, 6, 0, 0, 0, 0, 1, 3, 0, 0, 2, 0, 0, 3, 0]
  | 10 => [18, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, -6]
  | 11 => [9, 0, 9, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0]
  | 12 => [9, 0, 0, 0, 0, 0, 3, 0, 9, 0, 0, 0, 0, 0, 3, 0]
  | 13 => [-36, 18, 0, 0, 18, 0, 0, 0, 18, 0, 0, 0, 0, 6, 0, 0]
  | 14 => [18, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, -6]
  | 15 => [-36, 18, 18, 0, 18, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0]
  | 16 => [12, 0, 3, 0, 6, 0, 0, 3, -3, 0, 0, 0, 0, 1, 2, 0]
  | 17 => [18, 0, 0, 0, 0, 0, 0, -6, 18, 0, 0, 0, 0, 0, 0, -6]
  | 18 => [12, 3, -3, 0, 0, 0, 0, 0, 6, 0, 0, 2, 0, 3, 1, 0]
  | 19 => [12, 6, 3, 0, -3, 0, 0, 2, 0, 0, 0, 3, 0, 1, 0, 0]
  | 20 => [18, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, -6]
  | _ => [-36, 18, 18, 0, 0, 0, 0, 0, 18, 0, 0, 6, 0, 0, 0, 0]

private def certY4 (c : Fin 22) (b : Fin 16) : ℤ :=
  (certY4Row c).getD b.val 0

private def certYA4 (c : Fin 22) (a : Fin 16) : ℤ :=
  ((List.finRange 16).map fun b => e2Tensor4 b a * certY4 c b).sum

private def cap4Int (k : Fin 16) : ℕ :=
  let f := fin16ToBits4 k
  8 * (if f 0 then 1 else 3) * (if f 1 then 1 else 3) *
      (if f 2 then 1 else 3) * (if f 3 then 1 else 3)

private lemma cap4Int_eq (k : Fin 16) :
    ((cap4Int k : ℕ) : ℝ) / 2048 = muP (1 / 4 : ℝ) (fin16ToBits4 k) := by
  simp only [cap4Int, muP, Fin.prod_univ_four, slotWeight]
  cases fin16ToBits4 k 0 <;> cases fin16ToBits4 k 1 <;>
    cases fin16ToBits4 k 2 <;> cases fin16ToBits4 k 3 <;> norm_num

private lemma list_finRange_sum {n : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin n → M) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  rw [Fin.univ_def]
  simp [Finset.sum_mk]

private lemma certY4_sum_ne_dec :
    (List.finRange 22).all (fun c => ((List.finRange 16).map (certY4 c)).sum != 0) = true := by
  decide

private lemma certY4_loadB_dec :
    (List.finRange 16).all (fun b =>
      ((List.finRange 22).map (fun c => if certY4 c b != 0 then certPi4 c else 0)).sum ≤ cap4Int b) = true := by
  decide

private lemma certY4_loadA_dec :
    (List.finRange 16).all (fun a =>
      ((List.finRange 22).map (fun c => if certYA4 c a != 0 then certPi4 c else 0)).sum ≤ cap4Int a) = true := by
  decide

private lemma certPi4_sum_dec :
    ((List.finRange 22).map certPi4).sum = 456 := by
  decide

private lemma certY4_sum_ne (c : Fin 22) :
    ∑ b : Fin 16, certY4 c b ≠ 0 := by
  have h := List.all_eq_true.mp certY4_sum_ne_dec c (List.mem_finRange c)
  rw [← list_finRange_sum]
  simpa using h

private lemma certY4_loadB (b : Fin 16) :
    ∑ c : Fin 22, (if certY4 c b ≠ 0 then certPi4 c else 0) ≤ cap4Int b := by
  have h := List.all_eq_true.mp certY4_loadB_dec b (List.mem_finRange b)
  rw [← list_finRange_sum]
  simpa using h

private lemma certY4_loadA (a : Fin 16) :
    ∑ c : Fin 22, (if certYA4 c a ≠ 0 then certPi4 c else 0) ≤ cap4Int a := by
  have h := List.all_eq_true.mp certY4_loadA_dec a (List.mem_finRange a)
  rw [← list_finRange_sum]
  simpa using h

private lemma certPi4_sum : ∑ c : Fin 22, certPi4 c = 456 := by
  rw [← list_finRange_sum]; exact certPi4_sum_dec

private noncomputable def cert4 (c : Fin 22) : ReflCert (1 / 4 : ℝ) 4 where
  y := fun b => ((certY4 c (bits4Equiv b) : ℤ) : ℝ) / 24
  sum_ne := by
    rw [← Equiv.sum_comp bits4Equiv.symm
      (fun b => ((certY4 c (bits4Equiv b) : ℤ) : ℝ) / 24)]
    have heq : ∀ k : Fin 16, ((certY4 c (bits4Equiv (bits4Equiv.symm k)) : ℤ) : ℝ) / 24 =
        ((certY4 c k : ℤ) : ℝ) / 24 := by intro k; simp
    simp_rw [heq]
    rw [show (∑ k : Fin 16, ((certY4 c k : ℤ) : ℝ) / 24) =
        ((∑ k : Fin 16, certY4 c k : ℤ) : ℝ) / 24 by
      push_cast; rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun _ _ => by rw [div_eq_mul_inv]]
    apply div_ne_zero
    · exact_mod_cast certY4_sum_ne c
    · norm_num

private lemma cert4_yA_eq (c : Fin 22) (a : Fin 4 → Bool) :
    (cert4 c).yA a = ((certYA4 c (bits4Equiv a) : ℤ) : ℝ) / 384 := by
  have ha_eq : a = fin16ToBits4 (bits4Equiv a) := (bits4Equiv.symm_apply_apply a).symm
  dsimp only [ReflCert.yA, reflOpT, cert4]
  rw [← Equiv.sum_comp bits4Equiv.symm
    (fun b => (∏ i : Fin 4, reflE (1 / 4 : ℝ) (b i) (a i)) *
      (((certY4 c (bits4Equiv b) : ℤ) : ℝ) / 24))]
  have hterm : ∀ b : Fin 16,
      (∏ i : Fin 4, reflE (1 / 4 : ℝ) (bits4Equiv.symm b i) (a i)) *
        (((certY4 c (bits4Equiv (bits4Equiv.symm b)) : ℤ) : ℝ) / 24) =
      (((e2Tensor4 b (bits4Equiv a) * certY4 c b : ℤ) : ℝ)) / 384 := by
    intro b
    rw [bits4Equiv.apply_symm_apply]
    have hprod : ∏ i : Fin 4, reflE (1 / 4 : ℝ) (bits4Equiv.symm b i) (a i) =
        ((e2Tensor4 b (bits4Equiv a) : ℤ) : ℝ) / 16 := by
      rw [e2Tensor4_eq, ← ha_eq]; rfl
    rw [hprod]; push_cast; ring
  simp_rw [hterm]
  rw [show (∑ b : Fin 16, ((e2Tensor4 b (bits4Equiv a) * certY4 c b : ℤ) : ℝ) / 384) =
      ((∑ b : Fin 16, e2Tensor4 b (bits4Equiv a) * certY4 c b : ℤ) : ℝ) / 384 by
    push_cast; rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => by rw [div_eq_mul_inv]]
  have hya : (∑ b : Fin 16, e2Tensor4 b (bits4Equiv a) * certY4 c b) = certYA4 c (bits4Equiv a) :=
    (list_finRange_sum (fun b => e2Tensor4 b (bits4Equiv a) * certY4 c b)).symm
  rw [hya]

/-- **Verified 22-certificate `K = 4, p = 1/4` packing of value `57/256`.** -/
noncomputable def packing_K4_quarter : CertPacking (1 / 4 : ℝ) 4 where
  ι := Fin 22
  certs := cert4
  wt := fun c => ((certPi4 c : ℕ) : ℝ) / 2048
  wt_nonneg := fun c => by positivity
  loadA_le := fun a => by
    have ha_eq : a = fin16ToBits4 (bits4Equiv a) := (bits4Equiv.symm_apply_apply a).symm
    have hiff : ∀ c : Fin 22, ((cert4 c).yA a ≠ 0) ↔ (certYA4 c (bits4Equiv a) ≠ 0) := by
      intro c
      rw [cert4_yA_eq c a]
      constructor
      · intro h hz; apply h; simp [hz]
      · intro h hz; apply h
        have : ((certYA4 c (bits4Equiv a) : ℤ) : ℝ) = 0 := by linarith
        exact_mod_cast this
    calc ∑ c : Fin 22, (if (cert4 c).yA a ≠ 0 then ((certPi4 c : ℕ) : ℝ) / 2048 else 0)
        = ∑ c : Fin 22, (if certYA4 c (bits4Equiv a) ≠ 0 then ((certPi4 c : ℕ) : ℝ) / 2048 else 0) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            by_cases hc : certYA4 c (bits4Equiv a) ≠ 0
            · rw [if_pos ((hiff c).mpr hc), if_pos hc]
            · rw [if_neg (fun h => hc ((hiff c).mp h)), if_neg hc]
      _ = ((∑ c : Fin 22, if certYA4 c (bits4Equiv a) ≠ 0 then certPi4 c else 0 : ℕ) : ℝ) / 2048 := by
            rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
            refine Finset.sum_congr rfl fun c _ => by split_ifs <;> simp [div_eq_mul_inv]
      _ ≤ ((cap4Int (bits4Equiv a) : ℕ) : ℝ) / 2048 :=
            div_le_div_of_nonneg_right (by exact_mod_cast certY4_loadA (bits4Equiv a)) (by norm_num)
      _ = muP (1 / 4 : ℝ) a := by rw [cap4Int_eq, ← ha_eq]
  loadB_le := fun b => by
    have hb_eq : b = fin16ToBits4 (bits4Equiv b) := (bits4Equiv.symm_apply_apply b).symm
    have hiff : ∀ c : Fin 22, ((cert4 c).y b ≠ 0) ↔ (certY4 c (bits4Equiv b) ≠ 0) := by
      intro c
      dsimp only [cert4]
      constructor
      · intro h hz; apply h; simp [hz]
      · intro h hz; apply h
        have : ((certY4 c (bits4Equiv b) : ℤ) : ℝ) = 0 := by linarith
        exact_mod_cast this
    calc ∑ c : Fin 22, (if (cert4 c).y b ≠ 0 then ((certPi4 c : ℕ) : ℝ) / 2048 else 0)
        = ∑ c : Fin 22, (if certY4 c (bits4Equiv b) ≠ 0 then ((certPi4 c : ℕ) : ℝ) / 2048 else 0) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            by_cases hc : certY4 c (bits4Equiv b) ≠ 0
            · rw [if_pos ((hiff c).mpr hc), if_pos hc]
            · rw [if_neg (fun h => hc ((hiff c).mp h)), if_neg hc]
      _ = ((∑ c : Fin 22, if certY4 c (bits4Equiv b) ≠ 0 then certPi4 c else 0 : ℕ) : ℝ) / 2048 := by
            rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
            refine Finset.sum_congr rfl fun c _ => by split_ifs <;> simp [div_eq_mul_inv]
      _ ≤ ((cap4Int (bits4Equiv b) : ℕ) : ℝ) / 2048 :=
            div_le_div_of_nonneg_right (by exact_mod_cast certY4_loadB (bits4Equiv b)) (by norm_num)
      _ = muP (1 / 4 : ℝ) b := by rw [cap4Int_eq, ← hb_eq]

theorem packing_K4_quarter_value :
    packing_K4_quarter.value = 57 / 256 := by
  change (∑ c : Fin 22, ((certPi4 c : ℕ) : ℝ) / 2048) = 57 / 256
  have hsum : ∑ c : Fin 22, ((certPi4 c : ℕ) : ℝ) / 2048 =
      ((∑ c : Fin 22, certPi4 c : ℕ) : ℝ) / 2048 := by
    rw [div_eq_mul_inv, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => by rw [div_eq_mul_inv]
  rw [hsum, certPi4_sum]
  norm_num

end ExplicitPackings

section RateArithmetic

private lemma sqrt_two_lt_58_41 : Real.sqrt 2 < 58 / 41 := by
  rw [show (58 / 41 : ℝ) = Real.sqrt ((58 / 41) ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private lemma sqrt_two_lt_17_12 : Real.sqrt 2 < 17 / 12 := by
  rw [show (17 / 12 : ℝ) = Real.sqrt ((17 / 12) ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `2^(√2 - 2) < 2/3`. -/
theorem two_thirds_gt : (2 : ℝ) ^ (Real.sqrt 2 - 2) < 2 / 3 := by
  have h1 : (2 : ℝ) ^ (Real.sqrt 2 - 2) < (2 : ℝ) ^ (-(24 / 41 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [sqrt_two_lt_58_41])
  have hpow : ((2 : ℝ) ^ (-(24 / 41 : ℝ))) ^ (41 : ℕ) = ((2 : ℝ) ^ (24 : ℕ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (-(24 / 41 : ℝ)) * ((41 : ℕ) : ℝ) = -((24 : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ (-(24 / 41 : ℝ)) < 2 / 3 := by
    by_contra hc
    have hc := not_lt.mp hc
    have : ((2 : ℝ) / 3) ^ (41 : ℕ) ≤ ((2 : ℝ) ^ (-(24 / 41 : ℝ))) ^ (41 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hc 41
    rw [hpow] at this
    norm_num at this
  linarith

/-- `2^(4√2) < 57`, i.e., `4 · (57/256)^(1/4) > 2^√2`. -/
theorem k4_beats : (2 : ℝ) ^ (4 * Real.sqrt 2) < 57 := by
  have h1 : (2 : ℝ) ^ (4 * Real.sqrt 2) < (2 : ℝ) ^ (17 / 3 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [sqrt_two_lt_17_12])
  have hpow : ((2 : ℝ) ^ (17 / 3 : ℝ)) ^ (3 : ℕ) = (2 : ℝ) ^ (17 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (17 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((17 : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ (17 / 3 : ℝ) < 57 := by
    by_contra hc
    have hc := not_lt.mp hc
    have : (57 : ℝ) ^ (3 : ℕ) ≤ ((2 : ℝ) ^ (17 / 3 : ℝ)) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hc 3
    rw [hpow] at this
    norm_num at this
  linarith

private lemma shape_poly {m : ℝ} (hm : 3 ≤ m) : 4096 * m ^ 5 < (4 * m - 1) ^ 6 := by
  have h0 : 0 ≤ 11 / 3 * m := by linarith
  have h1 : (11 / 3 * m) ^ 6 ≤ (4 * m - 1) ^ 6 := pow_le_pow_left₀ h0 (by linarith) 6
  have hm5 : 0 < m ^ 5 := by positivity
  have h2 : 4096 * m ^ 5 < (11 / 3 * m) ^ 6 := by
    have e : (11 / 3 * m) ^ 6 = (11 / 3) ^ 6 * m * m ^ 5 := by ring
    rw [e]
    have : (4096 : ℝ) < (11 / 3) ^ 6 * m := by nlinarith
    nlinarith
  linarith

/-- For `m ≥ 3`, `m^(√2 - 2) < √((4m - 1) / (4m²))`. -/
theorem selfdual_rate_m3 {m : ℝ} (hm : 3 ≤ m) :
    m ^ (Real.sqrt 2 - 2) < Real.sqrt ((4 * m - 1) / (4 * m ^ 2)) := by
  have hm1 : 1 < m := by linarith
  have hm0 : 0 < m := by linarith
  have h1 : m ^ (Real.sqrt 2 - 2) < m ^ (-(7 / 12 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt hm1 (by nlinarith [sqrt_two_lt_17_12])
  set X := (4 * m - 1) / (4 * m ^ 2) with hX
  have hX0 : 0 < X := by rw [hX]; apply div_pos <;> nlinarith
  have hb : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hpa : (m ^ (-(7 / 12 : ℝ))) ^ (12 : ℕ) = (m ^ (7 : ℕ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    rw [show (-(7 / 12 : ℝ)) * ((12 : ℕ) : ℝ) = -((7 : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_neg hm0.le, Real.rpow_natCast]
  have hpb : (Real.sqrt X) ^ (12 : ℕ) = X ^ (6 : ℕ) := by
    rw [show (12 : ℕ) = 2 * 6 by norm_num, pow_mul, Real.sq_sqrt hX0.le]
  have hkey : (m ^ (7 : ℕ))⁻¹ < X ^ (6 : ℕ) := by
    rw [hX, div_pow]
    have hm7 : 0 < m ^ (7 : ℕ) := by positivity
    have hden : 0 < (4 * m ^ 2) ^ (6 : ℕ) := by positivity
    rw [inv_lt_iff_one_lt_mul₀' hm7, ← mul_div_assoc, one_lt_div hden]
    have hp := shape_poly hm
    have e : (4 * m ^ 2) ^ (6 : ℕ) = 4096 * m ^ 5 * m ^ 7 := by ring
    rw [e]
    have : 4096 * m ^ 5 * m ^ 7 < (4 * m - 1) ^ 6 * m ^ 7 :=
      mul_lt_mul_of_pos_right hp hm7
    linarith [this, show (4 * m - 1) ^ 6 * m ^ 7 = m ^ 7 * (4 * m - 1) ^ 6 by ring]
  have h2 : m ^ (-(7 / 12 : ℝ)) < Real.sqrt X := by
    by_contra hc
    have hc := not_lt.mp hc
    have : (Real.sqrt X) ^ (12 : ℕ) ≤ (m ^ (-(7 / 12 : ℝ))) ^ (12 : ℕ) :=
      pow_le_pow_left₀ hb.le hc 12
    rw [hpa, hpb] at this
    linarith
  linarith

private lemma sqrt_sum_sq_le_linear {L ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hℓL : ℓ ≤ L) :
    Real.sqrt (L ^ 2 + ℓ ^ 2) ≤ L + (Real.sqrt 2 - 1) * ℓ := by
  have hs2 : 1 ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
  have hrhs : 0 ≤ L + (Real.sqrt 2 - 1) * ℓ := by nlinarith
  rw [← Real.sqrt_sq hrhs]
  apply Real.sqrt_le_sqrt
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hprod : 0 ≤ (Real.sqrt 2 - 1) * ℓ * (L - ℓ) :=
    mul_nonneg (mul_nonneg (by linarith) hℓ) (by linarith)
  nlinarith

private lemma two_mul_ge_three_rate {r : ℕ} (hr : 3 ≤ r) :
    Real.sqrt (Real.log (r : ℝ) ^ 2 + Real.log 2 ^ 2) <
    Real.log ((r : ℝ) * 2 * (Real.sqrt 7 / 4)) := by
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hlog3_gt_one : (1 : ℝ) < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hL_ge : Real.log 3 ≤ Real.log (r : ℝ) :=
    Real.log_le_log (by norm_num) hrR
  have hlog74_gt : (1 / 2 : ℝ) < Real.log (7 / 4) := by
    rw [← Real.log_exp (1 / 2)]
    apply Real.log_lt_log (Real.exp_pos _)
    have hexp : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [sq, ← Real.exp_add]; norm_num
    have hlt : Real.exp (1 / 2) ^ 2 < (7 / 4 : ℝ) ^ 2 := by
      rw [hexp]; linarith [Real.exp_one_lt_d9]
    nlinarith [Real.exp_pos (1 / 2)]
  have hlog2_lt : Real.log 2 < 7 / 10 := by
    linarith [Real.log_two_lt_d9]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrhs_eq : Real.log ((r : ℝ) * 2 * (Real.sqrt 7 / 4)) =
      Real.log (r : ℝ) + Real.log (7 / 4) / 2 := by
    have h1 : (r : ℝ) * 2 * (Real.sqrt 7 / 4) = (r : ℝ) * Real.sqrt (7 / 4) := by
      rw [Real.sqrt_div (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      ring
    rw [h1, Real.log_mul hr0.ne' (Real.sqrt_pos.mpr (by norm_num)).ne', Real.log_sqrt (by norm_num)]
  rw [hrhs_eq]
  have hrhs_pos : 0 ≤ Real.log (r : ℝ) + Real.log (7 / 4) / 2 := by linarith
  rw [← Real.sqrt_sq hrhs_pos]
  apply Real.sqrt_lt_sqrt (by positivity)
  nlinarith

end RateArithmetic

section NoGoTheorem

private lemma reflection_wordSpan_nogo_le_half {r s n : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hn0 : 0 < n) (h2n : 2 * n ≤ r * s)
    (hslice : max r s ≤ 2 * n) :
    let D : ℝ := (r * s : ℕ)
    let p : ℝ := (n : ℝ) / D
    ∃ c > 0, ∃ g > 0,
      Real.sqrt (Real.log (r : ℝ) ^ 2 + Real.log (s : ℝ) ^ 2) < Real.log (D * g) ∧
      ∀ (K : ℕ) (h : (Fin K → Bool) → ℝ), c * (D * g) ^ K ≤ D ^ K * wordSpanCost p h := by
  intro D p
  have hD_pos : 0 < D := by
    have : 0 < r * s := by nlinarith
    dsimp only [D]
    exact_mod_cast this
  have hp0 : 0 < p := div_pos (by exact_mod_cast hn0) hD_pos
  have hp12 : p ≤ 1 / 2 := by
    dsimp only [p, D]
    rw [div_le_div_iff₀ hD_pos (by norm_num)]
    have : (2 * n : ℝ) ≤ (r * s : ℕ) := by exact_mod_cast h2n
    linarith
  have hp1 : p < 1 := by linarith
  have from_packing : ∀ {p' : ℝ} (hp'0 : 0 < p') (hp'1 : p' < 1) {B : ℕ} (hB : 0 < B)
      (P : CertPacking p' B) (hP : 0 < P.value),
      Real.sqrt (Real.log (r : ℝ) ^ 2 + Real.log (s : ℝ) ^ 2) <
        Real.log (D * P.value ^ ((1 : ℝ) / (B : ℝ))) →
      ∃ c > 0, ∃ g > 0,
        Real.sqrt (Real.log (r : ℝ) ^ 2 + Real.log (s : ℝ) ^ 2) < Real.log (D * g) ∧
        ∀ (K : ℕ) (h : (Fin K → Bool) → ℝ), c * (D * g) ^ K ≤ D ^ K * wordSpanCost p' h := by
    intro p' hp'0 hp'1 B hB P hP hrate
    let P1 := packing_K1_trivial hp'0 hp'1
    have hP1_pos : 0 < P1.value := by
      rw [packing_K1_trivial_value]; exact lt_min hp'0 (by linarith)
    obtain ⟨c, hc, hbound⟩ := P.asymptotic_bound hB hP P1 hP1_pos
    refine ⟨c, hc, P.value ^ ((1 : ℝ) / (B : ℝ)), Real.rpow_pos_of_pos hP _, hrate, fun K h => ?_⟩
    rw [mul_pow, show c * (D ^ K * (P.value ^ ((1 : ℝ) / (B : ℝ))) ^ K) =
      D ^ K * (c * (P.value ^ ((1 : ℝ) / (B : ℝ))) ^ K) by ring]
    exact mul_le_mul_of_nonneg_left (hbound K h) (pow_nonneg hD_pos.le K)
  by_cases hmin2 : min r s = 2
  · by_cases hmax2 : max r s = 2
    · have hr2 : r = 2 := by omega
      have hs2 : s = 2 := by omega
      subst hr2; subst hs2
      have hD4 : D = 4 := by norm_num [D]
      have hn_cases : n = 1 ∨ n = 2 := by omega
      rcases hn_cases with rfl | rfl
      · have hp_eq : p = 1 / 4 := by norm_num [p, D]
        have hP_pos : 0 < packing_K4_quarter.value := by rw [packing_K4_quarter_value]; norm_num
        rw [hp_eq]
        apply from_packing (by norm_num) (by norm_num) (by norm_num : 0 < 4) packing_K4_quarter hP_pos
        rw [packing_K4_quarter_value, hD4]
        push_cast
        have hlhs : Real.sqrt (Real.log (2 : ℝ) ^ 2 + Real.log (2 : ℝ) ^ 2) =
            Real.sqrt 2 * Real.log 2 := by
          rw [show Real.log (2 : ℝ) ^ 2 + Real.log (2 : ℝ) ^ 2 = 2 * Real.log (2 : ℝ) ^ 2 by ring,
            Real.sqrt_mul (by norm_num), Real.sqrt_sq (Real.log_pos (by norm_num)).le]
        rw [hlhs]
        have hrhs : Real.log (4 * (57 / 256 : ℝ) ^ ((1 : ℝ) / 4)) = Real.log 57 / 4 := by
          have h57 : (4 : ℝ) * (57 / 256 : ℝ) ^ ((1 : ℝ) / 4) = (57 : ℝ) ^ ((1 : ℝ) / 4) := by
            have h256 : (256 : ℝ) = 4 ^ (4 : ℕ) := by norm_num
            rw [Real.div_rpow (by norm_num) (by norm_num), h256,
              ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num; ring
          rw [h57, Real.log_rpow (by norm_num)]; ring
        rw [hrhs]
        have hlt : Real.log ((2 : ℝ) ^ (4 * Real.sqrt 2)) < Real.log 57 :=
          Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num) _) k4_beats
        rw [Real.log_rpow (by norm_num)] at hlt
        linarith
      · have hp_eq : p = 1 / 2 := by norm_num [p, D]
        let Pm := packing_K1_mid (p := p) (by linarith) (by linarith)
        have hPm_pos : 0 < Pm.value := by rw [packing_K1_mid_value]; norm_num
        apply from_packing hp0 hp1 (by norm_num : 0 < 1) Pm hPm_pos
        rw [packing_K1_mid_value, hD4]
        push_cast
        simp only [div_one, Real.rpow_one]
        have hlhs : Real.sqrt (Real.log (2 : ℝ) ^ 2 + Real.log (2 : ℝ) ^ 2) =
            Real.sqrt 2 * Real.log 2 := by
          rw [show Real.log (2 : ℝ) ^ 2 + Real.log (2 : ℝ) ^ 2 = 2 * Real.log (2 : ℝ) ^ 2 by ring,
            Real.sqrt_mul (by norm_num), Real.sqrt_sq (Real.log_pos (by norm_num)).le]
        rw [hlhs]
        have hlt : Real.log ((2 : ℝ) ^ (Real.sqrt 2 - 2)) < Real.log (2 / 3) :=
          Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num) _) two_thirds_gt
        rw [Real.log_rpow (by norm_num)] at hlt
        have h4 : Real.log (4 * (2 / 3 : ℝ)) = 2 * Real.log 2 + Real.log (2 / 3) := by
          rw [Real.log_mul (by norm_num) (by norm_num),
            show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
          push_cast; ring
        rw [h4]; linarith
    · set M : ℕ := max r s
      have hM3 : 3 ≤ M := by omega
      have hprod : r * s = M * 2 := by
        rcases le_total r s with hrs | hsr
        · have hr2 : r = 2 := by omega
          simp [M, max_eq_right hrs, hr2, mul_comm]
        · have hs2 : s = 2 := by omega
          simp [M, max_eq_left hsr, hs2]
      have hp14 : 1 / 4 ≤ p := by
        dsimp only [p, D]
        rw [div_le_div_iff₀ (by norm_num) hD_pos]
        have : r * s ≤ 4 * n := by omega
        have : ((r * s : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast this
        linarith
      have hrate_s74 : Real.sqrt (Real.log (r : ℝ) ^ 2 + Real.log (s : ℝ) ^ 2) <
          Real.log (D * (Real.sqrt 7 / 4)) := by
        have hD_eq : D = (M : ℝ) * 2 := by
          dsimp only [D]; exact_mod_cast hprod
        have hsq_eq : Real.log (r : ℝ) ^ 2 + Real.log (s : ℝ) ^ 2 =
            Real.log (M : ℝ) ^ 2 + Real.log 2 ^ 2 := by
          rcases le_total r s with hrs | hsr
          · have hr2 : r = 2 := by omega
            simp [M, max_eq_right hrs, hr2, add_comm]
          · have hs2 : s = 2 := by omega
            simp [M, max_eq_left hsr, hs2]
        rw [hD_eq, hsq_eq]
        exact two_mul_ge_three_rate hM3
      by_cases hp13 : p ≤ 1 / 3
      · let P2 := packing_K2 hp0 hp12
        have hP2_ge : 7 / 16 ≤ P2.value := by
          rw [packing_K2_value]
          exact le_min (by nlinarith) (by nlinarith)
        have hP2_pos : 0 < P2.value := by linarith
        apply from_packing hp0 hp1 (by norm_num : 0 < 2) P2 hP2_pos
        have hg_ge : Real.sqrt 7 / 4 ≤ P2.value ^ ((1 : ℝ) / (2 : ℕ)) := by
          rw [Nat.cast_ofNat, ← Real.sqrt_eq_rpow,
            show Real.sqrt 7 / 4 = Real.sqrt (7 / 16) by
              rw [Real.sqrt_div (by norm_num), show Real.sqrt 16 = 4 by
                rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
          exact Real.sqrt_le_sqrt hP2_ge
        exact lt_of_lt_of_le hrate_s74
          (Real.log_le_log (mul_pos hD_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)))
            (mul_le_mul_of_nonneg_left hg_ge hD_pos.le))
      · let Pm := packing_K1_mid (p := p) (by linarith) (by linarith)
        have hPm_pos : 0 < Pm.value := by rw [packing_K1_mid_value]; norm_num
        apply from_packing hp0 hp1 (by norm_num : 0 < 1) Pm hPm_pos
        rw [packing_K1_mid_value]
        simp only [Nat.cast_one, div_one, Real.rpow_one]
        have hge : Real.sqrt 7 / 4 ≤ 2 / 3 := by
          rw [div_le_iff₀ (by norm_num)]
          have : Real.sqrt 7 ^ 2 ≤ (8 / 3 : ℝ) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
          nlinarith [Real.sqrt_nonneg 7]
        exact lt_of_lt_of_le hrate_s74
          (Real.log_le_log (mul_pos hD_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)))
            (mul_le_mul_of_nonneg_left hge hD_pos.le))
  · set m : ℕ := min r s
    set M : ℕ := max r s
    have hm3 : 3 ≤ m := by omega
    have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hM0 : (0 : ℝ) < (M : ℝ) := by
      have : m ≤ M := le_trans (min_le_left r s) (le_max_left r s)
      have : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast this
      linarith
    have hD_eq : D = (M : ℝ) * (m : ℝ) := by
      have : r * s = M * m := by
        rcases le_total r s with hrs | hsr
        · simp [M, m, max_eq_right hrs, min_eq_left hrs, mul_comm]
        · simp [M, m, max_eq_left hsr, min_eq_right hsr]
      dsimp only [D]; exact_mod_cast this
    have hp_ge : 1 / (2 * (m : ℝ)) ≤ p := by
      dsimp only [p]
      rw [div_le_div_iff₀ (by positivity) hD_pos, hD_eq]
      have : (M : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hslice
      nlinarith
    set X : ℝ := (4 * (m : ℝ) - 1) / (4 * (m : ℝ) ^ 2) with hX
    have hX_pos : 0 < X := div_pos (by linarith) (by positivity)
    have hrate_X : Real.sqrt (Real.log (r : ℝ) ^ 2 + Real.log (s : ℝ) ^ 2) <
        Real.log (D * Real.sqrt X) := by
      have hsq_eq : Real.log (r : ℝ) ^ 2 + Real.log (s : ℝ) ^ 2 =
          Real.log (M : ℝ) ^ 2 + Real.log (m : ℝ) ^ 2 := by
        rcases le_total r s with hrs | hsr
        · simp [M, m, max_eq_right hrs, min_eq_left hrs, add_comm]
        · simp [M, m, max_eq_left hsr, min_eq_right hsr]
      rw [hsq_eq, hD_eq]
      have hℓ_pos : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
      have hℓL : Real.log (m : ℝ) ≤ Real.log (M : ℝ) := by
        apply Real.log_le_log hm0
        exact_mod_cast le_trans (min_le_left r s) (le_max_left r s)
      have hlin := sqrt_sum_sq_le_linear hℓ_pos hℓL
      have hsd := selfdual_rate_m3 hmR
      have hlog_sd : Real.log ((m : ℝ) ^ (Real.sqrt 2 - 2)) < Real.log (Real.sqrt X) :=
        Real.log_lt_log (Real.rpow_pos_of_pos hm0 _) hsd
      rw [Real.log_rpow hm0] at hlog_sd
      have hlogD : Real.log ((M : ℝ) * (m : ℝ) * Real.sqrt X) =
          Real.log (M : ℝ) + Real.log (m : ℝ) + Real.log (Real.sqrt X) := by
        rw [Real.log_mul (mul_pos hM0 hm0).ne' (Real.sqrt_pos.mpr hX_pos).ne',
          Real.log_mul hM0.ne' hm0.ne']
      rw [hlogD]
      linarith
    have hX_lt_49 : X ≤ 4 / 9 := by
      rw [hX, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    by_cases hp13 : p ≤ 1 / 3
    · let P2 := packing_K2 hp0 hp12
      have hP2_ge : X ≤ P2.value := by
        rw [packing_K2_value]
        apply le_min
        · have h1 : 2 * (1 / (2 * (m : ℝ))) - (1 / (2 * (m : ℝ))) ^ 2 = X := by
            rw [hX]; field_simp [hm0.ne']; ring
          rw [← h1]
          nlinarith
        · have : 4 / 9 ≤ (1 - p) ^ 2 := by nlinarith
          linarith
      have hP2_pos : 0 < P2.value := lt_of_lt_of_le hX_pos hP2_ge
      apply from_packing hp0 hp1 (by norm_num : 0 < 2) P2 hP2_pos
      have hg_ge : Real.sqrt X ≤ P2.value ^ ((1 : ℝ) / (2 : ℕ)) := by
        rw [Nat.cast_ofNat, ← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt hP2_ge
      exact lt_of_lt_of_le hrate_X
        (Real.log_le_log (mul_pos hD_pos (Real.sqrt_pos.mpr hX_pos))
          (mul_le_mul_of_nonneg_left hg_ge hD_pos.le))
    · let Pm := packing_K1_mid (p := p) (by linarith) (by linarith)
      have hPm_pos : 0 < Pm.value := by rw [packing_K1_mid_value]; norm_num
      apply from_packing hp0 hp1 (by norm_num : 0 < 1) Pm hPm_pos
      rw [packing_K1_mid_value]
      simp only [Nat.cast_one, div_one, Real.rpow_one]
      have hge : Real.sqrt X ≤ 2 / 3 := by
        rw [show (2 / 3 : ℝ) = Real.sqrt (4 / 9) by
          rw [show (4 / 9 : ℝ) = (2 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hX_lt_49
      exact lt_of_lt_of_le hrate_X
        (Real.log_le_log (mul_pos hD_pos (Real.sqrt_pos.mpr hX_pos))
          (mul_le_mul_of_nonneg_left hge hD_pos.le))

/-- **Reflection-type word-span no-go theorem:**
For every shape `r, s ≥ 2` and every reflection-type spectral multiplicity `0 < n < r * s`
satisfying the slice constraint `max r s ≤ 2 * min n (r * s - n)` (which holds automatically
for every exact reflection-type matrix decomposition by `reflection_slice_constraint`), there exist
constants `c > 0` and `g > 0` with `Real.log (r * s * g) > √((Real.log r)² + (Real.log s)²)` such
that for every tensor power `K` and every word-span evaluation `h : (Fin K → Bool) → ℝ`,
`c * (r * s * g) ^ K ≤ (r * s : ℝ) ^ K * wordSpanCost (n / (r * s)) h`. -/
theorem reflection_wordSpan_nogo {r s n : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hn0 : 0 < n) (hnD : n < r * s)
    (hslice : max r s ≤ 2 * min n (r * s - n)) :
    let D : ℝ := (r * s : ℕ)
    let p : ℝ := (n : ℝ) / D
    ∃ c > 0, ∃ g > 0,
      Real.sqrt (Real.log (r : ℝ) ^ 2 + Real.log (s : ℝ) ^ 2) < Real.log (D * g) ∧
      ∀ (K : ℕ) (h : (Fin K → Bool) → ℝ), c * (D * g) ^ K ≤ D ^ K * wordSpanCost p h := by
  intro D p
  by_cases h2n : 2 * n ≤ r * s
  · exact reflection_wordSpan_nogo_le_half hr hs hn0 h2n (le_trans hslice (by omega))
  · have hn'0 : 0 < r * s - n := by omega
    have h2n' : 2 * (r * s - n) ≤ r * s := by omega
    have hslice' : max r s ≤ 2 * (r * s - n) := le_trans hslice (by omega)
    obtain ⟨c, hc, g, hg, hrate, hbound⟩ :=
      reflection_wordSpan_nogo_le_half hr hs hn'0 h2n' hslice'
    refine ⟨c, hc, g, hg, hrate, fun K h => ?_⟩
    have hD_pos : (0 : ℝ) < D := by
      have : 0 < r * s := by nlinarith
      dsimp only [D]
      exact_mod_cast this
    have hp_sub : p = 1 - ((r * s - n : ℕ) : ℝ) / D := by
      dsimp only [p, D]
      have hle : n ≤ r * s := hnD.le
      rw [Nat.cast_sub hle]
      field_simp [hD_pos.ne']
      ring
    rw [hp_sub, wordSpanCost_one_sub]
    exact hbound K (fun x => h (fun i => !(x i)))

end NoGoTheorem

end PastaMath.TwoCutSoS
