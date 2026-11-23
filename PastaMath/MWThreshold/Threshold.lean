-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import PastaMath.MWThreshold.Literal

/-!
# The threshold of the Mudigonda–Williams BPTS calculus is the golden ratio

The literal calculus `MWL.Step` has threshold exactly φ = (1+√5)/2, both directions kernel-checked.

* `MWG.refutes_of_lt_phi`: for every c with 1 ≤ c and c(c−1) < 1 there is a strict refutation.
  Construction: the macro `M(j+1)` = one randomized speedup, j deterministic speedups, j+2 slowdowns,
  run under the (∃ n^0)^1 block that Theorem 2.10 leaves (`mac`). From kernel e = σ_{j+1}·T
  (σ_0 = 1, σ_{i+1} = σ_i + c^i, T ≥ 1) it reaches the same block with kernel ≤ c^{j+2}·T, so it
  multiplies the kernel by at most ρ = c^{j+2}/σ_{j+1}. If c(c−1) < 1 some j has ρ < 1
  (`exists_contracting`); the macro is iterated (`iter`) and the (∃ n^0)^1 block is popped once.
  The inner phase (`inner`) is an induction on the number of deterministic speedups left, with the
  invariant "kernel = σ_j·t, pin ≤ c^j·t, t ≥ 1"; every max(·,1) floor is resolved by t ≥ 1.
* `MWG.threshold_phi`: for c ≥ 1, (∃ refutation) ↔ c(c−1) < 1; `MWG.threshold_goldenRatio`:
  ↔ c < (1+√5)/2. `MWG.threshold_phi_U`, `MWG.threshold_phi_W` and `MWG.threshold_phi_X`: the
  same with the unmerged orientation of rule 4, with weakening as well, and with lines that need
  not alternate (combining and splitting same-type blocks at any time).
* `MWG.mw15_ok`: a 15-step refutation at c = 1467/1000, above the constant of the source paper's
  Theorem 5.3 (`MWG.mw21_root_lt`).
-/

namespace PastaMath.MWThreshold

namespace MWG

open MWL

/-- Reflexive–transitive closure of the literal step relation. -/
inductive Reach (c : ℝ) : Line → Line → Prop
  | refl (L : Line) : Reach c L L
  | tail {L M N : Line} : Reach c L M → Step c M N → Reach c L N

theorem Reach.trans {c : ℝ} {L M N : Line} (h1 : Reach c L M) (h2 : Reach c M N) : Reach c L N := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact Reach.tail ih hs

theorem Reach.single {c : ℝ} {L M : Line} (h : Step c L M) : Reach c L M :=
  Reach.tail (Reach.refl L) h

theorem Reach.head {c : ℝ} {L M N : Line} (h : Step c L M) (h2 : Reach c M N) : Reach c L N :=
  (Reach.single h).trans h2

theorem Reach.path {c : ℝ} {L M : Line} (h : Reach c L M) :
    ∃ (n : ℕ) (f : ℕ → Line), f 0 = L ∧ f n = M ∧ Path c f n := by
  induction h with
  | refl => exact ⟨0, fun _ => L, rfl, rfl, fun i hi => absurd hi (by omega)⟩
  | @tail M N _ hs ih =>
    obtain ⟨n, f, h0, hn, hst⟩ := ih
    classical
    refine ⟨n + 1, fun i => if i ≤ n then f i else N, by simp [h0], by simp, ?_⟩
    intro i hi
    by_cases h : i + 1 ≤ n
    · simp only [show i ≤ n by omega, h, if_true]; exact hst i (by omega)
    · have : i = n := by omega
      subst this
      simp only [le_refl, if_true, show ¬ i + 1 ≤ i by omega, if_false]
      rw [hn]; exact hs

/-- σ_0 = 1, σ_{j+1} = σ_j + c^j (so σ_j = 1 + Σ_{i<j} c^i). -/
noncomputable def sig (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => sig c j + c ^ j

theorem sig_succ (c : ℝ) (j : ℕ) : sig c (j + 1) = sig c j + c ^ j := rfl

theorem one_le_sig {c : ℝ} (hc : 0 ≤ c) : ∀ j, 1 ≤ sig c j
  | 0 => le_rfl
  | j + 1 => by rw [sig_succ]; have := one_le_sig hc j; have := pow_nonneg hc j; linarith

theorem sig_closed (c : ℝ) : ∀ j, (c - 1) * sig c j = c ^ j + c - 2
  | 0 => by simp [sig]; ring
  | j + 1 => by rw [sig_succ, mul_add, sig_closed c j, pow_succ]; ring

/-- Inner phase: j deterministic speedups and j+1 slowdowns, from a line whose innermost block is an
x·log n block.  Kernel σ_j·t, t ≥ 1, pin ≤ c^j·t ⟹ the line below is reached with a BPTS kernel
≤ c^{j+1}·t. -/
theorem inner {c : ℝ} (hc : 1 ≤ c) : ∀ (j : ℕ) (q : Bool) (R : List Blk) (a t : ℝ),
    a = sig c j * t → 1 ≤ t → pin R ≤ c ^ j * t →
    ∃ v, 0 ≤ v ∧ v ≤ c ^ (j + 1) * t ∧ Reach c (⟨q, 0, 1⟩ :: R, false, a) (R, true, v) := by
  have hc0 : 0 ≤ c := by linarith
  intro j
  induction j with
  | zero =>
    intro q R a t ha ht hp
    simp only [sig, one_mul, pow_zero] at ha hp
    refine ⟨c * max (max a 1) (max 0 (pin R)), ?_, ?_, Reach.single (Step.slow ⟨q, 0, 1⟩ R false a)⟩
    · exact mul_nonneg hc0 (le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_left _ _)))
    · rw [pow_one]
      exact mul_le_mul_of_nonneg_left
        (max_le (max_le (by linarith) ht) (max_le (by linarith) hp)) hc0
  | succ j ih =>
    intro q R a t ha ht hp
    rw [sig_succ] at ha
    have hcj : 1 ≤ c ^ j := one_le_pow₀ hc
    have hcj1 : c ^ j ≤ c ^ (j + 1) := pow_le_pow_right₀ hc (by omega)
    have hsj := one_le_sig hc0 j
    have hx1 : 1 ≤ c ^ j * t := by nlinarith
    have hxa : c ^ j * t < a := by rw [ha]; nlinarith
    have hd := Step.dspeed (c := c) ⟨q, 0, 1⟩ R a (c ^ j * t) (by linarith) hxa
    simp only [max_eq_right (show (0 : ℝ) ≤ c ^ j * t by linarith), max_eq_right hx1] at hd
    obtain ⟨v, hv0, hv, hr⟩ := ih (!q) (⟨q, c ^ j * t, c ^ j * t⟩ :: R) (a - c ^ j * t) t
      (by rw [ha]; ring) ht (by simp [pin])
    have hs := Step.slow (c := c) ⟨q, c ^ j * t, c ^ j * t⟩ R true v
    refine ⟨_, ?_, ?_, (Reach.head hd hr).tail hs⟩
    · exact mul_nonneg hc0 (le_trans hv0 (le_trans (le_max_left _ _) (le_max_left _ _)))
    · show c * max (max v (c ^ j * t)) (max (c ^ j * t) (pin R)) ≤ c ^ (j + 1 + 1) * t
      have hb : max (max v (c ^ j * t)) (max (c ^ j * t) (pin R)) ≤ c ^ (j + 1) * t := by
        have : c ^ j * t ≤ c ^ (j + 1) * t := mul_le_mul_of_nonneg_right hcj1 (by linarith)
        exact max_le (max_le hv this) (max_le this hp)
      calc c * max (max v (c ^ j * t)) (max (c ^ j * t) (pin R)) ≤ c * (c ^ (j + 1) * t) :=
            mul_le_mul_of_nonneg_left hb hc0
        _ = c ^ (j + 1 + 1) * t := by rw [pow_succ c (j + 1)]; ring

/-- The block (∃ n^0)^1 left by Theorem 2.10. -/
def top : Blk := ⟨true, 0, 1⟩

/-- One macro M(j+1) under the (∃ n^0)^1 block (or, from the empty line, creating it):
kernel σ_{j+1}·T ↦ kernel ≤ c^{j+2}·T. -/
theorem mac {c : ℝ} (hc : 1 ≤ c) (j : ℕ) (B0 : List Blk) (hB : B0 = [] ∨ B0 = [top]) (e T : ℝ)
    (he : e = sig c (j + 1) * T) (hT : 1 ≤ T) :
    ∃ e', 0 ≤ e' ∧ e' ≤ c ^ (j + 2) * T ∧ Reach c (B0, true, e) ([top], true, e') := by
  have hc0 : 0 ≤ c := by linarith
  rw [sig_succ] at he
  have hcj : 1 ≤ c ^ j := one_le_pow₀ hc
  have hcj1 : c ^ j ≤ c ^ (j + 1) := pow_le_pow_right₀ hc (by omega)
  have hsj := one_le_sig hc0 j
  have hx1 : 1 ≤ c ^ j * T := by nlinarith
  have hxa : c ^ j * T < e := by rw [he]; nlinarith
  set x := c ^ j * T with hxdef
  set R : List Blk := [⟨false, x, x⟩, top] with hR
  have hfirst : Step c (B0, true, e) (⟨true, 0, 1⟩ :: R, false, e - x) := by
    rcases hB with rfl | rfl
    · have h := Step.rspeed0 (c := c) e x (by linarith) hxa
      rw [max_eq_left hx1] at h
      exact h
    · have h : Step c ([top], true, e) ([⟨true, 0, 1⟩, ⟨false, x, max 1 x⟩, top], false, e - x) :=
        Step.rspeed top [] e x (by linarith) hxa
      rw [max_eq_right hx1] at h
      exact h
  obtain ⟨v, hv0, hv, hr⟩ := inner hc j true R (e - x) T (by rw [he]; ring) hT
    (by simp only [hR, pin]; exact le_rfl)
  have hs := Step.slow (c := c) ⟨false, x, x⟩ [top] true v
  refine ⟨_, ?_, ?_, (Reach.head hfirst hr).tail hs⟩
  · exact mul_nonneg hc0 (le_trans hv0 (le_trans (le_max_left _ _) (le_max_left _ _)))
  · show c * max (max v x) (max x (pin [top])) ≤ c ^ (j + 2) * T
    have hxx : x ≤ c ^ (j + 1) * T := mul_le_mul_of_nonneg_right hcj1 (by linarith)
    have h1 : (1 : ℝ) ≤ c ^ (j + 1) * T := le_trans hx1 hxx
    have hb : max (max v x) (max x (pin [top])) ≤ c ^ (j + 1) * T :=
      max_le (max_le hv hxx) (max_le hxx (by simp only [pin, top]; exact h1))
    calc c * max (max v x) (max x (pin [top])) ≤ c * (c ^ (j + 1) * T) :=
          mul_le_mul_of_nonneg_left hb hc0
      _ = c ^ (j + 2) * T := by rw [pow_succ c (j + 1)]; ring

/-- Iterating the macro under the block: after m rounds the kernel is ≤ max(ρ^m e, σ_{j+1}). -/
theorem iter {c : ℝ} (hc : 1 ≤ c) (j : ℕ) : ∀ (m : ℕ) (e : ℝ), 0 ≤ e →
    ∃ e', 0 ≤ e' ∧ e' ≤ max ((c ^ (j + 2) / sig c (j + 1)) ^ m * e) (sig c (j + 1)) ∧
      Reach c ([top], true, e) ([top], true, e') := by
  have hc0 : 0 ≤ c := by linarith
  have hs1 := one_le_sig hc0 (j + 1)
  set σ := sig c (j + 1) with hσ
  set ρ := c ^ (j + 2) / σ with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (pow_nonneg hc0 _) (by linarith)
  intro m
  induction m with
  | zero => intro e he; exact ⟨e, he, by simp, Reach.refl _⟩
  | succ m ih =>
    intro e he
    by_cases h : σ ≤ e
    · have hT : 1 ≤ e / σ := by rw [le_div_iff₀ (by linarith)]; linarith
      obtain ⟨e₁, he₁0, he₁, hr₁⟩ := mac hc j [top] (Or.inr rfl) e (e / σ)
        (by rw [← hσ]; field_simp) hT
      obtain ⟨e', he'0, he', hr'⟩ := ih e₁ he₁0
      refine ⟨e', he'0, le_trans he' (max_le_max ?_ le_rfl), hr₁.trans hr'⟩
      have : e₁ ≤ ρ * e := by
        rw [hρ]; calc e₁ ≤ c ^ (j + 2) * (e / σ) := he₁
          _ = c ^ (j + 2) / σ * e := by ring
      calc ρ ^ m * e₁ ≤ ρ ^ m * (ρ * e) := mul_le_mul_of_nonneg_left this (pow_nonneg hρ0 m)
        _ = ρ ^ (m + 1) * e := by ring
    · push Not at h
      exact ⟨e, he, le_trans h.le (le_max_right _ _), Reach.refl _⟩

/-- Bernoulli's inequality, in the form used below. -/
theorem bernoulli {c : ℝ} (hc : 1 ≤ c) : ∀ k : ℕ, 1 + k * (c - 1) ≤ c ^ k
  | 0 => by simp
  | k + 1 => by
      have := bernoulli hc k
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.2 this) (sub_nonneg.2 hc), one_le_pow₀ (n := k) hc]

/-- If c(c−1) < 1, some macro contracts: c^{j+2} < σ_{j+1}. -/
theorem exists_contracting {c : ℝ} (hc : 1 ≤ c) (hphi : c * (c - 1) < 1) :
    ∃ j : ℕ, c ^ (j + 2) < sig c (j + 1) := by
  rcases eq_or_lt_of_le hc with h | h
  · refine ⟨0, ?_⟩; subst h; simp [sig]
  · have hδ : 0 < 1 + c - c ^ 2 := by nlinarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((2 - c) / ((1 + c - c ^ 2) * (c - 1)))
    refine ⟨N, ?_⟩
    have hb := bernoulli hc (N + 1)
    have hcl := sig_closed c (N + 1)
    have hpos : 0 < (1 + c - c ^ 2) * (c - 1) := mul_pos hδ (by linarith)
    have hN' : 2 - c < N * ((1 + c - c ^ 2) * (c - 1)) := by
      rw [div_lt_iff₀ hpos] at hN; linarith
    have hk : 2 - c < c ^ (N + 1) * (1 + c - c ^ 2) := by
      have : (N : ℝ) * ((1 + c - c ^ 2) * (c - 1)) ≤ c ^ (N + 1) * (1 + c - c ^ 2) := by
        have h2 : (N : ℝ) * (c - 1) ≤ c ^ (N + 1) := by push_cast at hb; nlinarith
        nlinarith
      linarith
    have : (c - 1) * c ^ (N + 2) < (c - 1) * sig c (N + 1) := by
      rw [hcl, pow_succ c (N + 1)]; nlinarith
    exact lt_of_mul_lt_mul_left this (by linarith)

/-- **Refutations for every c < φ** in MW21's literal calculus. -/
theorem refutes_of_lt_phi {c : ℝ} (hc : 1 ≤ c) (hphi : c * (c - 1) < 1) :
    ∃ n M, Refutes c n M := by
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨j, hj⟩ := exists_contracting hc hphi
  have hs1 := one_le_sig hc0 (j + 1)
  set σ := sig c (j + 1) with hσ
  set ρ := c ^ (j + 2) / σ with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (pow_nonneg hc0 _) (by linarith)
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one (by linarith)]; exact hj
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / c by positivity) hρ1
  set a₀ := c * σ + 1 with ha₀
  have ha₀σ : σ ≤ a₀ := by nlinarith
  have hT : 1 ≤ a₀ / σ := by rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨e₁, he₁0, he₁, hr₁⟩ := mac hc j [] (Or.inl rfl) a₀ (a₀ / σ) (by rw [← hσ]; field_simp) hT
  obtain ⟨e', he'0, he', hr'⟩ := iter hc j m e₁ he₁0
  have hfin := Step.slow (c := c) top [] true e'
  obtain ⟨n, f, h0, hn, hp⟩ := (hr₁.trans hr').path
  refine ⟨n + 1, fun i => if i ≤ n then f i else ([], true, c * max (max e' top.o)
    (max top.g (pin []))), by omega, ?_, a₀, c * max (max e' top.o) (max top.g (pin [])),
    by positivity, by simp [h0], by simp, ?_⟩
  · intro i hi
    by_cases h : i + 1 ≤ n
    · simp only [show i ≤ n by omega, h, if_true]; exact hp i (by omega)
    · have : i = n := by omega
      subst this
      simp only [le_refl, if_true, show ¬ i + 1 ≤ i by omega, if_false]
      rw [hn]; exact hfin
  · simp only [top, pin]
    have he₁' : e₁ ≤ ρ * a₀ := by
      rw [hρ]; calc e₁ ≤ c ^ (j + 2) * (a₀ / σ) := he₁
        _ = c ^ (j + 2) / σ * a₀ := by ring
    have hρm : ρ ^ m * ρ < 1 / c := lt_of_le_of_lt (by nlinarith [pow_nonneg hρ0 m]) hm
    have hcm : c * (ρ ^ m * ρ) < 1 := by
      rw [lt_div_iff₀ (by linarith)] at hρm; linarith
    have hpos : 0 < a₀ := by positivity
    have hA : c * (ρ ^ m * e₁) < a₀ := by
      have : ρ ^ m * e₁ ≤ ρ ^ m * (ρ * a₀) := mul_le_mul_of_nonneg_left he₁' (pow_nonneg hρ0 m)
      nlinarith
    have hB : c * σ < a₀ := by linarith
    have hmax : max (max e' 1) (max 0 1) ≤ max (ρ ^ m * e₁) σ := by
      refine max_le (max_le he' (le_trans hs1 (le_max_right _ _)))
        (max_le (le_trans (by linarith) (le_max_right _ _)) (le_trans hs1 (le_max_right _ _)))
    calc c * max (max e' 1) (max 0 1) ≤ c * max (ρ ^ m * e₁) σ := mul_le_mul_of_nonneg_left hmax hc0
      _ < a₀ := by
        rcases le_total (ρ ^ m * e₁) σ with h | h
        · rw [max_eq_right h]; exact hB
        · rw [max_eq_left h]; exact hA

/-- **Threshold of MW21's BPTS calculus, both directions kernel-checked.** For c ≥ 1 there is a strict
refutation iff c(c−1) < 1. -/
theorem threshold_phi {c : ℝ} (hc : 1 ≤ c) : (∃ n M, Refutes c n M) ↔ c * (c - 1) < 1 := by
  constructor
  · rintro ⟨n, M, h⟩
    by_contra hn
    push Not at hn
    exact no_lit_refutation (by linarith) (by nlinarith) n M h
  · exact refutes_of_lt_phi hc

/-- The same with the golden ratio φ = (1+√5)/2 written out. -/
theorem threshold_goldenRatio {c : ℝ} (hc : 1 ≤ c) :
    (∃ n M, Refutes c n M) ↔ c < Real.goldenRatio := by
  rw [threshold_phi hc]
  have h1 := Real.one_lt_goldenRatio
  have h2 := Real.goldenRatio_sq
  constructor
  · intro h; by_contra hn; push Not at hn; nlinarith
  · intro h; nlinarith

/-- With both orientations of the randomized speedup the literal calculus is still capped at φ, and
the construction above is unchanged (it uses only `Step`). -/
theorem threshold_phi_U {c : ℝ} (hc : 1 ≤ c) :
    ((∃ n M, RefutesU c n M) ↔ c * (c - 1) < 1) := by
  constructor
  · rintro ⟨n, M, h⟩
    by_contra hn
    push Not at hn
    exact no_litU_refutation (by linarith) (by nlinarith) n M h
  · intro h
    obtain ⟨n, M, hn, hp, a₀, a', ha, h0, hN, hlt⟩ := refutes_of_lt_phi hc h
    exact ⟨n, M, hn, fun i hi => StepU.lit (hp i hi), a₀, a', ha, h0, hN, hlt.le⟩

/-- With weakening added as well (raising exponents of an existing line, TS ⊆ BPTS), the threshold
is unchanged. The left side asks only for a non-strict refutation with at least one rule step. -/
theorem threshold_phi_W {c : ℝ} (hc : 1 ≤ c) :
    ((∃ n M, RefutesW c n M) ↔ c * (c - 1) < 1) := by
  constructor
  · rintro ⟨n, M, h⟩
    by_contra hn
    push Not at hn
    exact no_litW_refutation (by linarith) (by nlinarith) n M h
  · intro h
    obtain ⟨n, M, hn, hp, a₀, a', ha, h0, hN, hlt⟩ := refutes_of_lt_phi hc h
    exact ⟨n, M, fun i hi => StepW.rule (StepU.lit (hp i hi)), ⟨0, hn, StepU.lit (hp 0 hn)⟩,
      a₀, a', ha, h0, hN, hlt.le⟩

/-- With lines that need not alternate, combining and splitting adjacent same-type blocks anywhere
in the prefix at any later time, Lemma 2.7 with Q = Q_k unmerged, both orientations of rule 4 and
weakening, the threshold is unchanged. The left side asks only for a non-strict refutation in which
some line has a quantifier block. -/
theorem threshold_phi_X {c : ℝ} (hc : 1 ≤ c) :
    ((∃ n M, RefutesX c n M) ↔ c * (c - 1) < 1) := by
  constructor
  · rintro ⟨n, M, h⟩
    by_contra hn
    push Not at hn
    exact no_litX_refutation (by linarith) (by nlinarith) n M h
  · intro h
    obtain ⟨n, M, hn, hp, a₀, a', ha, h0, hN, hlt⟩ := refutes_of_lt_phi hc h
    have h1 := hp 0 hn
    rw [h0] at h1
    exact ⟨n, M, fun i hi => step_stepX (hp i hi), ⟨1, hn, step_nil_ne h1⟩,
      a₀, a', ha, h0, hN, hlt.le⟩

/-! ### A 15-step refutation at c = 1.467: M(3) M(3), then the final slowdown -/

def mw15 : List Tag :=
  [.r 3830, .d (206250 / 79), .d (105000 / 59), .s, .s, .s, .s,
   .r (1550000 / 491), .d (170000 / 79), .d (1040000 / 709), .s, .s, .s, .s, .s]

theorem mw15_ok : checkQ (1467 / 1000) 10000 mw15 = true := by decide +kernel

theorem mw15_refutes : ∃ n M, Refutes (1467 / 1000 : ℝ) n M := by
  have h := checkQ_sound mw15_ok; push_cast at h; exact h

/-- Every real root of x³ − x² − 1 (the source paper's Theorem 5.3; largest root ≈ 1.4656) is
below 1467/1000, so `mw15_refutes` is a refutation beyond that constant. -/
theorem mw21_root_lt {x : ℝ} (h : x ^ 3 - x ^ 2 - 1 = 0) : x < 1467 / 1000 := by
  by_contra hc
  push Not at hc
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ x = 1467 / 1000 + t := ⟨x - 1467 / 1000, by linarith, by ring⟩
  have e : (1467 / 1000 + t) ^ 3 - (1467 / 1000 + t) ^ 2 - 1 =
      t ^ 3 + 3401 / 1000 * t ^ 2 + 3522267 / 1000000 * t + 5025563 / 1000000000 := by ring
  rw [e] at h
  nlinarith [pow_nonneg ht 3, sq_nonneg t]

end MWG
end PastaMath.MWThreshold
