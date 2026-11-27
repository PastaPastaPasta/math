-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith

namespace PastaMath.FastDiag

open Finset

section Konig

variable {E α β : Type*} [DecidableEq E] [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [DecidableEq E] [Fintype α] [DecidableEq α] in
theorem card_filter_mem_eq_sum {γ : Type*} [DecidableEq γ] (L : E → γ) (S : Finset E)
    (s : Finset γ) :
    (S.filter (fun e => L e ∈ s)).card = ∑ a ∈ s, (S.filter (fun e => L e = a)).card := by
  rw [card_eq_sum_card_fiberwise (f := L) (t := s)
    (fun e he => by simpa using (mem_filter.mp he).2)]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ ha⟩, h3⟩

omit [DecidableEq E] in
theorem card_eq_mul_of_fibers (L : E → α) (S : Finset E) (r : ℕ)
    (hL : ∀ a, (S.filter (fun e => L e = a)).card = r) :
    S.card = r * Fintype.card α := by
  rw [card_eq_sum_card_fiberwise (f := L) (t := univ) (fun _ _ => mem_coe.mpr (mem_univ _))]
  simp [hL, mul_comm]

theorem regular_bipartite_coloring (L : E → α) (R : E → β) :
    ∀ (r : ℕ) (S : Finset E), (∀ a, (S.filter (fun e => L e = a)).card = r) →
      (∀ b, (S.filter (fun e => R e = b)).card = r) →
      ∃ col : E → ℕ, (∀ e ∈ S, col e < r) ∧
        (∀ e ∈ S, ∀ e' ∈ S, L e = L e' → col e = col e' → e = e') ∧
        (∀ e ∈ S, ∀ e' ∈ S, R e = R e' → col e = col e' → e = e') := by
  intro r
  induction r with
  | zero =>
    intro S hL _
    have hS : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      have h := hL (L e)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
      exact h he rfl
    subst hS
    exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  | succ r ih =>
    intro S hL hR
    set t : α → Finset β := fun a => (S.filter (fun e => L e = a)).image R with ht
    have hall : ∀ s : Finset α, s.card ≤ (s.biUnion t).card := by
      intro s
      have h1 : (S.filter (fun e => L e ∈ s)).card = (r + 1) * s.card := by
        rw [card_filter_mem_eq_sum L S s, Finset.sum_congr rfl (fun a _ => hL a)]
        simp [mul_comm]
      have h2 : (S.filter (fun e => R e ∈ s.biUnion t)).card = (r + 1) * (s.biUnion t).card := by
        rw [card_filter_mem_eq_sum R S (s.biUnion t), Finset.sum_congr rfl (fun b _ => hR b)]
        simp [mul_comm]
      have h3 : S.filter (fun e => L e ∈ s) ⊆ S.filter (fun e => R e ∈ s.biUnion t) := by
        intro e he
        rw [mem_filter] at he ⊢
        refine ⟨he.1, ?_⟩
        rw [mem_biUnion]
        exact ⟨L e, he.2, mem_image.mpr ⟨e, mem_filter.mpr ⟨he.1, rfl⟩, rfl⟩⟩
      have h4 := card_le_card h3
      rw [h1, h2] at h4
      exact Nat.le_of_mul_le_mul_left h4 (Nat.succ_pos r)
    obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
    have hg : ∀ a, ∃ e, e ∈ S ∧ L e = a ∧ R e = f a := by
      intro a
      obtain ⟨e, he, hfe⟩ := mem_image.mp (hft a)
      exact ⟨e, (mem_filter.mp he).1, (mem_filter.mp he).2, hfe⟩
    choose g hgS hgL hgR using hg
    have hcard : Fintype.card α = Fintype.card β := by
      have e1 := card_eq_mul_of_fibers L S (r + 1) hL
      have e2 := card_eq_mul_of_fibers R S (r + 1) hR
      rw [e1] at e2
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos r) e2
    have hfbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩
    set M : Finset E := univ.image g with hM
    have hmemM : ∀ e, e ∈ M ↔ ∃ a, g a = e := by
      intro e; simp [hM]
    set S' := S \ M with hS'
    have hL' : ∀ a, (S'.filter (fun e => L e = a)).card = r := by
      intro a
      have : S'.filter (fun e => L e = a) = (S.filter (fun e => L e = a)).erase (g a) := by
        ext e
        simp only [hS', mem_filter, mem_sdiff, mem_erase, hmemM]
        constructor
        · rintro ⟨⟨heS, hnM⟩, hLe⟩
          exact ⟨fun h => hnM ⟨a, h.symm⟩, heS, hLe⟩
        · rintro ⟨hne, heS, hLe⟩
          refine ⟨⟨heS, ?_⟩, hLe⟩
          rintro ⟨a', rfl⟩
          rw [hgL] at hLe
          exact hne (hLe ▸ rfl)
      rw [this, card_erase_of_mem (mem_filter.mpr ⟨hgS a, hgL a⟩), hL a]
      rfl
    have hR' : ∀ b, (S'.filter (fun e => R e = b)).card = r := by
      intro b
      obtain ⟨a₀, ha₀⟩ := hfbij.2 b
      have : S'.filter (fun e => R e = b) = (S.filter (fun e => R e = b)).erase (g a₀) := by
        ext e
        simp only [hS', mem_filter, mem_sdiff, mem_erase, hmemM]
        constructor
        · rintro ⟨⟨heS, hnM⟩, hRe⟩
          exact ⟨fun h => hnM ⟨a₀, h.symm⟩, heS, hRe⟩
        · rintro ⟨hne, heS, hRe⟩
          refine ⟨⟨heS, ?_⟩, hRe⟩
          rintro ⟨a', rfl⟩
          rw [hgR, ← ha₀] at hRe
          exact hne (hfinj hRe ▸ rfl)
      rw [this, card_erase_of_mem (mem_filter.mpr ⟨hgS a₀, by rw [hgR, ha₀]⟩), hR b]
      rfl
    obtain ⟨col', hcol'lt, hcol'L, hcol'R⟩ := ih S' hL' hR'
    classical
    refine ⟨fun e => if e ∈ M then r else col' e, ?_, ?_, ?_⟩
    · intro e he
      by_cases h : e ∈ M
      · simp [h]
      · simp only [h, if_false]
        exact Nat.lt_succ_of_lt (hcol'lt e (mem_sdiff.mpr ⟨he, h⟩))
    · intro e he e' he' hLL hcc
      by_cases h : e ∈ M <;> by_cases h' : e' ∈ M
      · obtain ⟨a, rfl⟩ := (hmemM e).mp h
        obtain ⟨a', rfl⟩ := (hmemM e').mp h'
        rw [hgL, hgL] at hLL
        rw [hLL]
      · simp only [h, h', if_true, if_false] at hcc
        exact absurd hcc.symm (Nat.ne_of_lt (hcol'lt e' (mem_sdiff.mpr ⟨he', h'⟩)))
      · simp only [h, h', if_true, if_false] at hcc
        exact absurd hcc (Nat.ne_of_lt (hcol'lt e (mem_sdiff.mpr ⟨he, h⟩)))
      · simp only [h, h', if_false] at hcc
        exact hcol'L e (mem_sdiff.mpr ⟨he, h⟩) e' (mem_sdiff.mpr ⟨he', h'⟩) hLL hcc
    · intro e he e' he' hRR hcc
      by_cases h : e ∈ M <;> by_cases h' : e' ∈ M
      · obtain ⟨a, rfl⟩ := (hmemM e).mp h
        obtain ⟨a', rfl⟩ := (hmemM e').mp h'
        rw [hgR, hgR] at hRR
        rw [hfinj hRR]
      · simp only [h, h', if_true, if_false] at hcc
        exact absurd hcc.symm (Nat.ne_of_lt (hcol'lt e' (mem_sdiff.mpr ⟨he', h'⟩)))
      · simp only [h, h', if_true, if_false] at hcc
        exact absurd hcc (Nat.ne_of_lt (hcol'lt e (mem_sdiff.mpr ⟨he, h⟩)))
      · simp only [h, h', if_false] at hcc
        exact hcol'R e (mem_sdiff.mpr ⟨he, h⟩) e' (mem_sdiff.mpr ⟨he', h'⟩) hRR hcc

end Konig

theorem perm_of_injective {n : ℕ} (f : Fin n → Fin n) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, σ i = f i :=
  ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun _ => rfl⟩

theorem clos_rearrangeable {q r : ℕ} (ψ : Fin q × Fin r ≃ Fin q × Fin r) :
    ∃ (s1 : Fin q → Equiv.Perm (Fin r)) (s2 : Fin r → Equiv.Perm (Fin q))
      (s3 : Fin q → Equiv.Perm (Fin r)),
      ∀ a i, (s2 (s1 a i) a, s3 (s2 (s1 a i) a) (s1 a i)) = ψ (a, i) := by
  classical
  have hLf : ∀ a : Fin q, ((univ : Finset (Fin q × Fin r)).filter
      (fun z => z.1 = a)).card = r := by
    intro a
    have : (univ : Finset (Fin q × Fin r)).filter (fun z => z.1 = a)
        = (univ : Finset (Fin r)).map ⟨fun i => (a, i), fun i j h => by simpa using h⟩ := by
      ext z; simp [Prod.ext_iff, eq_comm]
    rw [this, card_map, card_univ, Fintype.card_fin]
  have hRf : ∀ b : Fin q, ((univ : Finset (Fin q × Fin r)).filter
      (fun z => (ψ z).1 = b)).card = r := by
    intro b
    have : (univ : Finset (Fin q × Fin r)).filter (fun z => (ψ z).1 = b)
        = ((univ : Finset (Fin q × Fin r)).filter (fun w => w.1 = b)).map
            ψ.symm.toEmbedding := by
      ext z
      simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
      constructor
      · intro h; exact ⟨ψ z, h, by simp⟩
      · rintro ⟨w, hw, rfl⟩; simpa using hw
    rw [this, card_map, hLf b]
  obtain ⟨col, hlt, hcL, hcR⟩ := regular_bipartite_coloring (fun z : Fin q × Fin r => z.1)
    (fun z => (ψ z).1) r univ hLf hRf
  let c : Fin q × Fin r → Fin r := fun z => ⟨col z, hlt z (mem_univ z)⟩
  have hcLinj : ∀ z z', z.1 = z'.1 → c z = c z' → z = z' := fun z z' h1 h2 =>
    hcL z (mem_univ _) z' (mem_univ _) h1 (congrArg Fin.val h2)
  have hcRinj : ∀ z z', (ψ z).1 = (ψ z').1 → c z = c z' → z = z' := fun z z' h1 h2 =>
    hcR z (mem_univ _) z' (mem_univ _) h1 (congrArg Fin.val h2)
  have hs1 : ∀ a, ∃ σ : Equiv.Perm (Fin r), ∀ i, σ i = c (a, i) := fun a =>
    perm_of_injective _ (fun i j h => by
      have := hcLinj (a, i) (a, j) rfl h
      simpa using this)
  choose s1 hs1 using hs1
  have hs2 : ∀ k, ∃ σ : Equiv.Perm (Fin q), ∀ a, σ a = (ψ (a, (s1 a).symm k)).1 := fun k =>
    perm_of_injective _ (fun a a' h => by
      have hk : c (a, (s1 a).symm k) = c (a', (s1 a').symm k) := by
        rw [← hs1, ← hs1]; simp
      have := hcRinj _ _ h hk
      exact congrArg Prod.fst this)
  choose s2 hs2 using hs2
  have hs3 : ∀ b : Fin q, ∃ σ : Equiv.Perm (Fin r),
      ∀ z, (ψ z).1 = b → σ (c z) = (ψ z).2 := by
    intro b
    let F := {z : Fin q × Fin r // (ψ z).1 = b}
    have hFcard : Fintype.card F = r := by
      rw [Fintype.card_subtype]; exact hRf b
    let φ : F → Fin r := fun z => c z.1
    let χ : F → Fin r := fun z => (ψ z.1).2
    have hφ : Function.Bijective φ := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨fun z z' h => Subtype.ext (hcRinj _ _ (z.2.trans z'.2.symm) h), by simp [hFcard]⟩
    have hχ : Function.Bijective χ := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨fun z z' h => Subtype.ext (ψ.injective (Prod.ext (z.2.trans z'.2.symm) h)),
        by simp [hFcard]⟩
    refine ⟨(Equiv.ofBijective φ hφ).symm.trans (Equiv.ofBijective χ hχ), fun z hz => ?_⟩
    have : (Equiv.ofBijective φ hφ).symm (c z) = ⟨z, hz⟩ :=
      (Equiv.ofBijective φ hφ).symm_apply_eq.mpr rfl
    simp only [Equiv.trans_apply, this, Equiv.ofBijective_apply, χ]
  choose s3 hs3 using hs3
  refine ⟨s1, s2, s3, fun a i => ?_⟩
  have h2 : s2 (s1 a i) a = (ψ (a, i)).1 := by rw [hs2]; simp
  rw [h2, hs1, hs3 _ (a, i) rfl]


end PastaMath.FastDiag
