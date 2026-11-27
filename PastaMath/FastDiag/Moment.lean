-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PastaMath.FastDiag

open Finset

theorem even_tuples_card_le {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) :
    (univ.filter (fun v : Fin (2 * k) → α =>
      ∀ a, Even (univ.filter (fun i => v i = a)).card)).card
      ≤ k ^ (2 * k) * Fintype.card α ^ k := by
  classical
  have hsub : univ.filter (fun v : Fin (2 * k) → α =>
      ∀ a, Even (univ.filter (fun i => v i = a)).card) ⊆
      univ.image (fun p : (Fin (2 * k) → Fin k) × (Fin k → α) => p.2 ∘ p.1) := by
    intro v hv
    rw [mem_filter] at hv
    obtain ⟨-, hev⟩ := hv
    rw [mem_image]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨(fun i => absurd i.2 (by simp), fun j => absurd j.2 (by simp)), mem_univ _, ?_⟩
      funext i
      exact absurd i.2 (by simp)
    set S := univ.image v with hS
    have hcard : S.card ≤ k := by
      have h1 : (univ : Finset (Fin (2 * k))).card
          = ∑ a ∈ S, (univ.filter (fun i => v i = a)).card :=
        card_eq_sum_card_image v univ
      have h2 : ∀ a ∈ S, 2 ≤ (univ.filter (fun i => v i = a)).card := by
        intro a ha
        obtain ⟨i, -, rfl⟩ := mem_image.mp ha
        have hpos : 0 < (univ.filter (fun j => v j = v i)).card :=
          card_pos.mpr ⟨i, by simp⟩
        obtain ⟨r, hr⟩ := hev (v i)
        omega
      have h3 : S.card • 2 ≤ ∑ a ∈ S, (univ.filter (fun i => v i = a)).card :=
        card_nsmul_le_sum S _ 2 h2
      have h3' : S.card * 2 ≤ ∑ a ∈ S, (univ.filter (fun i => v i = a)).card := h3
      simp only [card_univ, Fintype.card_fin] at h1
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (α := {x // x ∈ S}) (β := Fin k) (by simpa using hcard)
    have hmem : ∀ i, v i ∈ S := fun i => mem_image_of_mem v (mem_univ i)
    refine ⟨(fun i => e ⟨v i, hmem i⟩,
      Function.extend (fun a : {x // x ∈ S} => e a) (fun a => (a : α))
        (fun _ => v ⟨0, by omega⟩)), mem_univ _, ?_⟩
    funext i
    simp only [Function.comp_apply]
    exact e.injective.extend_apply (fun a : {x // x ∈ S} => (a : α)) _ ⟨v i, hmem i⟩
  calc (univ.filter (fun v : Fin (2 * k) → α =>
        ∀ a, Even (univ.filter (fun i => v i = a)).card)).card
      ≤ (univ.image (fun p : (Fin (2 * k) → Fin k) × (Fin k → α) => p.2 ∘ p.1)).card :=
        card_le_card hsub
    _ ≤ (univ : Finset ((Fin (2 * k) → Fin k) × (Fin k → α))).card := card_image_le
    _ = k ^ (2 * k) * Fintype.card α ^ k := by
        simp [Fintype.card_prod]

def sgn (b : Bool) : ℤ := if b then -1 else 1

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> simp [sgn]

theorem sum_bool_sgn_pow (c : ℕ) :
    ∑ b : Bool, sgn b ^ c = if Even c then 2 else 0 := by
  rw [Fintype.sum_bool]
  rcases Nat.even_or_odd c with h | h
  · simp [sgn, h.neg_one_pow, h]
  · have hne : ¬ Even c := Nat.not_even_iff_odd.mpr h
    simp [sgn, h.neg_one_pow, hne]

theorem sum_tables_prod_sgn {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) :
    ∑ T : ι → Bool, ∏ i, sgn (T i) ^ c i
      = if ∀ i, Even (c i) then 2 ^ Fintype.card ι else 0 := by
  rw [← Fintype.prod_sum (fun i b => sgn b ^ c i)]
  simp_rw [sum_bool_sgn_pow]
  split_ifs with hall
  · rw [Finset.prod_congr rfl (fun i _ => if_pos (hall i))]
    simp
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

theorem sum_partial_table_prod_sgn {Z : Type*} [Fintype Z] [DecidableEq Z]
    (U : Finset Z) (T0 : Z → Bool) (c : Z → ℕ) :
    ∑ S : U → Bool, ∏ y, sgn (if h : y ∈ U then S ⟨y, h⟩ else T0 y) ^ c y
      = (if ∀ y ∈ U, Even (c y) then 2 ^ U.card else 0) *
          ∏ y ∈ univ.filter (fun y => y ∉ U), sgn (T0 y) ^ c y := by
  have hsplit : ∀ S : U → Bool, ∏ y, sgn (if h : y ∈ U then S ⟨y, h⟩ else T0 y) ^ c y
      = (∏ y : U, sgn (S y) ^ c y) *
          ∏ y ∈ univ.filter (fun y => y ∉ U), sgn (T0 y) ^ c y := by
    intro S
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun y => y ∈ U)]
    congr 1
    · have hU : univ.filter (fun y => y ∈ U) = U := by
        ext y; simp
      rw [hU, ← Finset.prod_coe_sort U]
      refine Finset.prod_congr rfl (fun y _ => ?_)
      simp [y.2]
    · refine Finset.prod_congr rfl (fun y hy => ?_)
      simp [(mem_filter.mp hy).2]
  simp_rw [hsplit, ← Finset.sum_mul]
  congr 1
  rw [sum_tables_prod_sgn (fun y : U => c y)]
  simp [Subtype.forall]

section Potential

variable {X Δ Ω : Type*} [Fintype X] [DecidableEq X] [Fintype Δ] [Fintype Ω]

def corr (g F : X → Bool) : ℤ := ∑ x, sgn (g x) * sgn (F x)

omit [DecidableEq X] in
theorem corr_self (g : X → Bool) : corr g g = Fintype.card X := by
  simp [corr, sgn_mul_self]

omit [DecidableEq X] in
theorem corr_pow_expand (g F : X → Bool) (u : ℕ) :
    corr g F ^ u = ∑ x : Fin u → X, (∏ i, sgn (g (x i))) * ∏ i, sgn (F (x i)) := by
  rw [corr, Fintype.sum_pow]
  simp [Finset.prod_mul_distrib]

theorem abs_prod_sgn {u : ℕ} (f : Fin u → Bool) : |∏ i, sgn (f i)| = 1 := by
  rw [Finset.abs_prod]
  simp [abs_sgn]

theorem potential_sum_le (C : Δ → X → Bool) (F : Ω → X → Bool) (u : ℕ)
    (Good : Finset (Fin u → X))
    (hB : ∀ x : Fin u → X,
      ∑ ω, ∏ i, sgn (F ω (x i)) = if x ∈ Good then (Fintype.card Ω : ℤ) else 0) :
    ∑ ω, ∑ d, corr (C d) (F ω) ^ u
      ≤ (Fintype.card Δ : ℤ) * Good.card * Fintype.card Ω := by
  have hexp : ∑ ω, ∑ d, corr (C d) (F ω) ^ u
      = ∑ d, ∑ x : Fin u → X, (∏ i, sgn (C d (x i))) *
          (if x ∈ Good then (Fintype.card Ω : ℤ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp_rw [corr_pow_expand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.mul_sum, hB x]
  rw [hexp]
  have hterm : ∀ d, ∀ x : Fin u → X, (∏ i, sgn (C d (x i))) *
      (if x ∈ Good then (Fintype.card Ω : ℤ) else 0)
      ≤ (if x ∈ Good then (Fintype.card Ω : ℤ) else 0) := by
    intro d x
    have hnn : (0 : ℤ) ≤ (if x ∈ Good then (Fintype.card Ω : ℤ) else 0) := by
      split_ifs <;> positivity
    have h1 : (∏ i, sgn (C d (x i))) ≤ 1 := by
      have := le_abs_self (∏ i, sgn (C d (x i)))
      rw [abs_prod_sgn (fun i => C d (x i))] at this
      exact this
    nlinarith
  calc ∑ d, ∑ x : Fin u → X, (∏ i, sgn (C d (x i))) *
          (if x ∈ Good then (Fintype.card Ω : ℤ) else 0)
      ≤ ∑ _d : Δ, ∑ x : Fin u → X, (if x ∈ Good then (Fintype.card Ω : ℤ) else 0) :=
        Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun x _ => hterm d x))
    _ = (Fintype.card Δ : ℤ) * Good.card * Fintype.card Ω := by
        rw [Finset.sum_const, Finset.card_univ, ← Finset.sum_filter]
        simp [mul_assoc]

omit [DecidableEq X] in
theorem potential_ge_count (C : Δ → X → Bool) (F : X → Bool) {u : ℕ} (hu : Even u)
    (d₀ : Δ) (hd₀ : C d₀ = F) :
    (Fintype.card X : ℤ) ^ u ≤ ∑ d, corr (C d) F ^ u := by
  have hnn : ∀ d ∈ (univ : Finset Δ), 0 ≤ corr (C d) F ^ u := fun d _ => hu.pow_nonneg _
  have := Finset.single_le_sum hnn (mem_univ d₀)
  rw [hd₀, corr_self] at this
  exact this

theorem exists_hard_of_potential [Nonempty Ω] (C : Δ → X → Bool) (F : Ω → X → Bool) {u : ℕ}
    (hu : Even u) (Good : Finset (Fin u → X))
    (hB : ∀ x : Fin u → X,
      ∑ ω, ∏ i, sgn (F ω (x i)) = if x ∈ Good then (Fintype.card Ω : ℤ) else 0)
    (hlt : Fintype.card Δ * Good.card < Fintype.card X ^ u) :
    ∃ ω, ∀ d, C d ≠ F ω := by
  by_contra hcon
  push Not at hcon
  have hlow : (Fintype.card Ω : ℤ) * (Fintype.card X : ℤ) ^ u
      ≤ ∑ ω, ∑ d, corr (C d) (F ω) ^ u := by
    have := Finset.sum_le_sum (fun ω (_ : ω ∈ (univ : Finset Ω)) =>
      (let ⟨d₀, hd₀⟩ := hcon ω; potential_ge_count C (F ω) hu d₀ hd₀))
    simpa [Finset.sum_const, Finset.card_univ] using this
  have hup := potential_sum_le C F u Good hB
  have hΩ : (0 : ℤ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hlt' : (Fintype.card Δ : ℤ) * Good.card < (Fintype.card X : ℤ) ^ u := by
    exact_mod_cast hlt
  nlinarith

end Potential

section BlockXor

variable {t : ℕ} {Y : Fin t → Type*} [∀ ℓ, Fintype (Y ℓ)] [∀ ℓ, DecidableEq (Y ℓ)]

def blockXor (T : ∀ ℓ, Y ℓ → Bool) (x : ∀ ℓ, Y ℓ) : Bool :=
  decide (Odd (univ.filter (fun ℓ => T ℓ (x ℓ) = true)).card)

omit [∀ ℓ, Fintype (Y ℓ)] [∀ ℓ, DecidableEq (Y ℓ)] in
theorem sgn_blockXor (T : ∀ ℓ, Y ℓ → Bool) (x : ∀ ℓ, Y ℓ) :
    sgn (blockXor T x) = ∏ ℓ, sgn (T ℓ (x ℓ)) := by
  have hprod : ∏ ℓ, sgn (T ℓ (x ℓ)) = (-1) ^ (univ.filter (fun ℓ => T ℓ (x ℓ) = true)).card := by
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun ℓ => T ℓ (x ℓ) = true)]
    have h1 : ∏ ℓ ∈ univ.filter (fun ℓ => T ℓ (x ℓ) = true), sgn (T ℓ (x ℓ))
        = ∏ _ℓ ∈ univ.filter (fun ℓ => T ℓ (x ℓ) = true), (-1 : ℤ) :=
      Finset.prod_congr rfl (fun ℓ hℓ => by simp [sgn, (mem_filter.mp hℓ).2])
    have h2 : ∏ ℓ ∈ univ.filter (fun ℓ => ¬ T ℓ (x ℓ) = true), sgn (T ℓ (x ℓ))
        = ∏ _ℓ ∈ univ.filter (fun ℓ => ¬ T ℓ (x ℓ) = true), (1 : ℤ) :=
      Finset.prod_congr rfl (fun ℓ hℓ => by simp [sgn, (mem_filter.mp hℓ).2])
    rw [h1, h2, Finset.prod_const, Finset.prod_const_one, mul_one]
  rw [hprod, blockXor]
  rcases Nat.even_or_odd (univ.filter (fun ℓ => T ℓ (x ℓ) = true)).card with h | h
  · have hne : ¬ Odd (univ.filter (fun ℓ => T ℓ (x ℓ) = true)).card := Nat.not_odd_iff_even.mpr h
    simp [sgn, hne, h.neg_one_pow]
  · simp [sgn, h, h.neg_one_pow]

def blockGood (u : ℕ) : Finset (Fin u → ∀ ℓ, Y ℓ) :=
  univ.filter (fun x => ∀ ℓ, ∀ y : Y ℓ, Even (univ.filter (fun i => x i ℓ = y)).card)

theorem prod_sgn_fiber {u : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (T : Z → Bool) (w : Fin u → Z) :
    ∏ i, sgn (T (w i)) = ∏ y, sgn (T y) ^ (univ.filter (fun i => w i = y)).card := by
  rw [Finset.prod_comp (s := univ) (fun y => sgn (T y)) w]
  refine Finset.prod_subset (subset_univ _) (fun y _ hy => ?_)
  have : (univ.filter (fun i => w i = y)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    exact hy (mem_image.mpr ⟨i, mem_univ _, hi⟩)
  simp [this]

theorem blockXor_sign_sum (u : ℕ) (x : Fin u → ∀ ℓ, Y ℓ) :
    ∑ T : (∀ ℓ, Y ℓ → Bool), ∏ i, sgn (blockXor T (x i))
      = if x ∈ blockGood u then (Fintype.card (∀ ℓ, Y ℓ → Bool) : ℤ) else 0 := by
  simp_rw [sgn_blockXor]
  have hswap : ∀ T : (∀ ℓ, Y ℓ → Bool),
      ∏ i, ∏ ℓ, sgn (T ℓ (x i ℓ)) = ∏ ℓ, ∏ i, sgn (T ℓ (x i ℓ)) :=
    fun T => Finset.prod_comm
  simp_rw [hswap]
  rw [← Fintype.prod_sum (fun ℓ (Tℓ : Y ℓ → Bool) => ∏ i, sgn (Tℓ (x i ℓ)))]
  have hblock : ∀ ℓ, ∑ Tℓ : Y ℓ → Bool, ∏ i, sgn (Tℓ (x i ℓ))
      = if ∀ y : Y ℓ, Even (univ.filter (fun i => x i ℓ = y)).card
        then 2 ^ Fintype.card (Y ℓ) else 0 := by
    intro ℓ
    simp_rw [prod_sgn_fiber _ (fun i => x i ℓ)]
    exact sum_tables_prod_sgn (fun y => (univ.filter (fun i => x i ℓ = y)).card)
  simp_rw [hblock]
  by_cases hx : x ∈ blockGood u
  · rw [if_pos hx]
    have hall : ∀ ℓ, ∀ y : Y ℓ, Even (univ.filter (fun i => x i ℓ = y)).card := by
      simpa [blockGood] using hx
    rw [Finset.prod_congr rfl (fun ℓ _ => if_pos (hall ℓ))]
    simp [Fintype.card_pi]
  · rw [if_neg hx]
    have : ∃ ℓ, ¬ ∀ y : Y ℓ, Even (univ.filter (fun i => x i ℓ = y)).card := by
      by_contra h
      push Not at h
      exact hx (by simpa [blockGood] using h)
    obtain ⟨ℓ, hℓ⟩ := this
    exact Finset.prod_eq_zero (mem_univ ℓ) (by simp [hℓ])

def mergeTables (U : ∀ ℓ, Finset (Y ℓ)) (T0 : ∀ ℓ, Y ℓ → Bool) (S : ∀ ℓ, U ℓ → Bool) :
    ∀ ℓ, Y ℓ → Bool :=
  fun ℓ y => if h : y ∈ U ℓ then S ℓ ⟨y, h⟩ else T0 ℓ y

theorem blockXor_partial_sign_sum (u : ℕ) (U : ∀ ℓ, Finset (Y ℓ)) (T0 : ∀ ℓ, Y ℓ → Bool)
    (x : Fin u → ∀ ℓ, Y ℓ) :
    ∑ S : (∀ ℓ, U ℓ → Bool), ∏ i, sgn (blockXor (mergeTables U T0 S) (x i))
      = ∏ ℓ, ((if ∀ y ∈ U ℓ, Even (univ.filter (fun i => x i ℓ = y)).card
            then 2 ^ (U ℓ).card else 0) *
          ∏ y ∈ univ.filter (fun y => y ∉ U ℓ),
            sgn (T0 ℓ y) ^ (univ.filter (fun i => x i ℓ = y)).card) := by
  simp_rw [sgn_blockXor]
  have hswap : ∀ S : (∀ ℓ, U ℓ → Bool),
      ∏ i, ∏ ℓ, sgn (mergeTables U T0 S ℓ (x i ℓ))
        = ∏ ℓ, ∏ i, sgn (mergeTables U T0 S ℓ (x i ℓ)) :=
    fun S => Finset.prod_comm
  simp_rw [hswap]
  simp only [mergeTables]
  rw [← Fintype.prod_sum (fun ℓ (Sℓ : U ℓ → Bool) =>
    ∏ i, sgn (if h : x i ℓ ∈ U ℓ then Sℓ ⟨x i ℓ, h⟩ else T0 ℓ (x i ℓ)))]
  refine Finset.prod_congr rfl (fun ℓ _ => ?_)
  rw [← sum_partial_table_prod_sgn (U ℓ) (T0 ℓ)]
  refine Finset.sum_congr rfl (fun Sℓ _ => ?_)
  exact prod_sgn_fiber (fun y => if h : y ∈ U ℓ then Sℓ ⟨y, h⟩ else T0 ℓ y) (fun i => x i ℓ)

theorem blockGood_card_le (k : ℕ) :
    (blockGood (Y := Y) (2 * k)).card ≤ ∏ ℓ, k ^ (2 * k) * Fintype.card (Y ℓ) ^ k := by
  classical
  let E : ∀ ℓ, Finset (Fin (2 * k) → Y ℓ) := fun ℓ =>
    univ.filter (fun v : Fin (2 * k) → Y ℓ => ∀ a, Even (univ.filter (fun i => v i = a)).card)
  have hinj : Set.InjOn (fun (x : Fin (2 * k) → ∀ ℓ, Y ℓ) ℓ i => x i ℓ)
      (blockGood (Y := Y) (2 * k) : Set (Fin (2 * k) → ∀ ℓ, Y ℓ)) := by
    intro x _ x' _ h
    funext i ℓ
    exact congrFun (congrFun h ℓ) i
  have hmaps : ∀ x ∈ blockGood (Y := Y) (2 * k),
      (fun (x : Fin (2 * k) → ∀ ℓ, Y ℓ) ℓ i => x i ℓ) x ∈ Fintype.piFinset E := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro ℓ
    have hall : ∀ ℓ, ∀ y : Y ℓ, Even (univ.filter (fun i => x i ℓ = y)).card := by
      simpa [blockGood] using hx
    simp [E, hall ℓ]
  calc (blockGood (Y := Y) (2 * k)).card ≤ (Fintype.piFinset E).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = ∏ ℓ, (E ℓ).card := Fintype.card_piFinset E
    _ ≤ ∏ ℓ, k ^ (2 * k) * Fintype.card (Y ℓ) ^ k :=
        Finset.prod_le_prod' (fun ℓ _ => even_tuples_card_le k)

theorem exists_hard_blockXor {Δ : Type*} [Fintype Δ] (C : Δ → (∀ ℓ, Y ℓ) → Bool) (k : ℕ)
    (hlt : Fintype.card Δ * ∏ ℓ, (k ^ (2 * k) * Fintype.card (Y ℓ) ^ k)
      < (∏ ℓ, Fintype.card (Y ℓ)) ^ (2 * k)) :
    ∃ T : (∀ ℓ, Y ℓ → Bool), ∀ d, C d ≠ blockXor T := by
  have hgood := blockGood_card_le (Y := Y) k
  refine exists_hard_of_potential C (fun T => blockXor T) (u := 2 * k) (even_two_mul k)
    (blockGood (2 * k)) (fun x => blockXor_sign_sum (2 * k) x) ?_
  rw [Fintype.card_pi]
  calc Fintype.card Δ * (blockGood (Y := Y) (2 * k)).card
      ≤ Fintype.card Δ * ∏ ℓ, (k ^ (2 * k) * Fintype.card (Y ℓ) ^ k) :=
        Nat.mul_le_mul_left _ hgood
    _ < (∏ ℓ, Fintype.card (Y ℓ)) ^ (2 * k) := hlt

end BlockXor

end PastaMath.FastDiag
