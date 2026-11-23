-- SPDX-License-Identifier: Apache-2.0
import PastaMath.TautThreshold.Literal

/-!
The DvMW family (W13 Theorem 6.7, Claim 1) as normal-form proofs in W13's §6 calculus
with the **exact** rules of Lemmas 6.1/6.2 (`TW.WStepE`, including Lemma 6.1's side conditions
b ≥ 1, a ≥ 1 and the input constraint 1 of the outermost block). Result `nf_exists`: for every
c with 1 ≤ c and c³ < 4 there is a normal-form proof (`TW.NF (TW.WStepE c)`); with
`TW.no_nf` the threshold of the literal calculus is exactly ∛4 (`threshold_literal`).

Stage statement (`MacE c s R`): for every scale l ≥ R, from K[n^{s·l}] one derives
(Q n^l)^l (Q̄ n^{g})^{w} K̄[n^κ] with 1 ≤ w ≤ l, g ≤ w, κ ≤ l, where Q is the quantifier of
the kernel's type, both when the innermost block is of the other type (two blocks opened) and
when it is of type Q with guess ≤ l and input constraint 1 (merged). Stage s gives stage
1 + s²/c³ at R' = c³R, as in W13's proof (the previous stage is used twice).
-/

namespace PastaMath.TautThreshold
namespace TDL

open TW

inductive DNW (c : ℝ) : WLine → WLine → Prop
  | refl (L : WLine) : DNW c L L
  | tail {L M N : WLine} : DNW c L M → WStepE c M N → N.1 ≠ [] → DNW c L N

theorem DNW.trans {c : ℝ} {L M N : WLine} (h1 : DNW c L M) (h2 : DNW c M N) : DNW c L N := by
  induction h2 with
  | refl => exact h1
  | tail _ hs hn ih => exact DNW.tail ih hs hn

theorem DNW.single {c : ℝ} {L M : WLine} (h : WStepE c L M) (hM : M.1 ≠ []) : DNW c L M :=
  DNW.tail (DNW.refl L) h hM

theorem DNW.seq {c : ℝ} {L M : WLine} (h : DNW c L M) :
    ∃ (n : ℕ) (f : ℕ → WLine), f 0 = L ∧ f n = M ∧ (∀ i < n, WStepE c (f i) (f (i + 1))) ∧
      (∀ i, 0 < i → i ≤ n → (f i).1 ≠ []) := by
  induction h with
  | refl => exact ⟨0, fun _ => L, rfl, rfl, fun i hi => absurd hi (by omega),
      fun i h1 h2 => absurd h1 (by omega)⟩
  | @tail M N _ hs hn ih =>
    obtain ⟨n, f, h0, hn', hst, hne⟩ := ih
    classical
    refine ⟨n + 1, fun i => if i ≤ n then f i else N, by simp [h0], by simp, ?_, ?_⟩
    · intro i hi
      by_cases h : i + 1 ≤ n
      · simp only [show i ≤ n by omega, h, if_true]; exact hst i (by omega)
      · have : i = n := by omega
        subst this
        simp only [le_refl, if_true, show ¬ i + 1 ≤ i by omega, if_false]
        rw [hn']; exact hs
    · intro i h1 h2
      by_cases h : i ≤ n
      · simp only [h, if_true]; exact hne i h1 h
      · simp only [h, if_false]; exact hn

theorem max4 {a b c d m : ℝ} (ha : a ≤ m) (hb : b ≤ m) (hc : c ≤ m) (hd : d ≤ m)
    (hm : a = m ∨ b = m ∨ c = m ∨ d = m) : max (max a b) (max c d) = m := by
  apply le_antisymm (max_le (max_le ha hb) (max_le hc hd))
  rcases hm with h | h | h | h
  · rw [← h]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  · rw [← h]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  · rw [← h]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  · rw [← h]; exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem popE {c : ℝ} (u : Blk) (rest : List Blk) (k : Bool) (a e : ℝ) (hq : u.q = k)
    (he : c * max (max u.g a) (max u.o (pin rest)) = e) :
    WStepE c (u :: rest, k, a) (rest, !k, e) := by
  rw [← he]; exact WStepE.pop u rest k a hq

theorem flipE {c : ℝ} (u : Blk) (rest : List Blk) (k : Bool) (a e : ℝ) (hq : u.q ≠ k)
    (he : c * max a u.o = e) : WStepE c (u :: rest, k, a) (u :: rest, !k, e) := by
  rw [← he]; exact WStepE.flip u rest k a hq

theorem nb (k : Bool) (g o : ℝ) (rest : List Blk) : ((⟨k, g, o⟩ : Blk) :: rest) ≠ [] :=
  List.cons_ne_nil _ _

/-- What a stage does after its first speedup. -/
def InnerE (c s R : ℝ) : Prop :=
  ∀ (P : List Blk) (k : Bool) (l : ℝ), R ≤ l →
    ∃ w g κ, 1 ≤ w ∧ w ≤ l ∧ g ≤ w ∧ κ ≤ l ∧
      DNW c (⟨!k, 0, 1⟩ :: ⟨k, l, l⟩ :: P, k, s * l - l) (⟨!k, g, w⟩ :: ⟨k, l, l⟩ :: P, !k, κ)

def MacE (c s R : ℝ) : Prop :=
  (∀ (P : List Blk) (k : Bool) (l : ℝ), R ≤ l → pin P = 1 → (∀ u rest, P = u :: rest → u.q ≠ k) →
    ∃ w g κ, 1 ≤ w ∧ w ≤ l ∧ g ≤ w ∧ κ ≤ l ∧
      DNW c (P, k, s * l) (⟨!k, g, w⟩ :: ⟨k, l, l⟩ :: P, !k, κ)) ∧
  (∀ (g₀ : ℝ) (rest : List Blk) (k : Bool) (l : ℝ), R ≤ l → g₀ ≤ l →
    ∃ w g κ, 1 ≤ w ∧ w ≤ l ∧ g ≤ w ∧ κ ≤ l ∧
      DNW c (⟨k, g₀, 1⟩ :: rest, k, s * l) (⟨!k, g, w⟩ :: ⟨k, l, l⟩ :: rest, !k, κ))

theorem macE_of_inner {c s R : ℝ} (hR : 1 ≤ R) (hs : 1 ≤ s) (hI : InnerE c s R) : MacE c s R := by
  constructor
  · intro P k l hl hp hq
    have hl1 : 1 ≤ l := le_trans hR hl
    have h1 := WStepE.speedNew (c := c) P k (s * l) l hq (by rw [hp]) (by nlinarith) (by linarith)
    rw [hp, max_eq_right hl1] at h1
    obtain ⟨w, g, κ, h₁, h₂, h₃, h₄, hd⟩ := hI P k l hl
    exact ⟨w, g, κ, h₁, h₂, h₃, h₄, (DNW.single h1 (nb _ _ _ _)).trans hd⟩
  · intro g₀ rest k l hl hg
    have hl1 : 1 ≤ l := le_trans hR hl
    have h1 := WStepE.speedMerge (c := c) ⟨k, g₀, 1⟩ rest k (s * l) l rfl le_rfl (by nlinarith)
      (by linarith)
    simp only at h1
    rw [max_eq_right hg, max_eq_right hl1] at h1
    obtain ⟨w, g, κ, h₁, h₂, h₃, h₄, hd⟩ := hI rest k l hl
    exact ⟨w, g, κ, h₁, h₂, h₃, h₄, (DNW.single h1 (nb _ _ _ _)).trans hd⟩

/-- W13's stage 2: NTS[n^{(1+1/c)l}] ⊆ (∃ n^l)^l (∀ log n)¹ NTS[n^{l/c}] ⊆ (∃ n^l)^l (∀ log n)¹ coNTS[n^l]
(kernel exponents stay ≥ 1 for l ≥ c). -/
theorem innerE_base {c R : ℝ} (hc : 1 ≤ c) (hR : c ≤ R) : InnerE c (1 + 1 / c) R := by
  intro P k l hl
  have hc0 : 0 < c := by linarith
  have hlc : 1 ≤ l / c := by rw [le_div_iff₀ hc0]; linarith
  have h1 := flipE (c := c) ⟨!k, 0, 1⟩ (⟨k, l, l⟩ :: P) k ((1 + 1 / c) * l - l) l (by simp)
    (by
      simp only
      rw [show (1 + 1 / c) * l - l = l / c by field_simp; ring, max_eq_left hlc]
      field_simp)
  exact ⟨1, 0, l, le_rfl, by linarith, zero_le_one, le_rfl, DNW.single h1 (nb _ _ _ _)⟩

/-- **The DvMW stage, in the exact calculus.** -/
theorem innerE_step {c s R : ℝ} (hc : 1 ≤ c) (hR : 1 ≤ R) (hs : 1 ≤ s) (hM : MacE c s R) :
    InnerE c (1 + s ^ 2 / c ^ 3) (c ^ 3 * R) := by
  intro P k l hl
  have hc0 : 0 < c := by linarith
  have hc3 : 1 ≤ c ^ 3 := one_le_pow₀ hc
  have hc2 : c ≤ c ^ 3 := by
    have h2 : 1 ≤ c ^ 2 := one_le_pow₀ hc
    nlinarith [mul_le_mul_of_nonneg_left h2 (le_of_lt hc0)]
  have hl1 : 1 ≤ l := le_trans (one_le_mul_of_one_le_of_one_le hc3 hR) hl
  have hsl : l ≤ s * l := by nlinarith
  set μ := s * l / c ^ 3 with hμ
  set ν := l / c with hν
  have hRμ : R ≤ μ := by
    rw [hμ, le_div_iff₀ (by positivity)]
    linarith
  have hRν : R ≤ ν := by
    rw [hν, le_div_iff₀ hc0]
    have : c * R ≤ c ^ 3 * R := mul_le_mul_of_nonneg_right hc2 (by linarith)
    linarith
  have hμ1 : 1 ≤ μ := le_trans hR hRμ
  have hν1 : 1 ≤ ν := le_trans hR hRν
  have hcμ : μ ≤ c * μ := by nlinarith
  have hk : (1 + s ^ 2 / c ^ 3) * l - l = s * μ := by rw [hμ]; ring
  have hk2 : c * (c * μ) = s * ν := by rw [hμ, hν]; field_simp
  have hcν : c * ν = l := by rw [hν]; field_simp
  have hνl : ν ≤ l := by rw [hν, div_le_iff₀ hc0]; nlinarith
  rw [hk]
  set C₁ : List Blk := ⟨!k, 0, 1⟩ :: ⟨k, l, l⟩ :: P with hC₁
  -- first use of stage s (innermost block ∀-type relative to the kernel: two blocks opened)
  obtain ⟨w₁, g₁, κ₁, hw₁, hw₁', hg₁, hκ₁, d1⟩ :=
    hM.1 C₁ k μ hRμ rfl (fun u rest he => by
      rw [hC₁] at he; simp only [List.cons.injEq] at he; rw [← he.1]; simp)
  -- pop the index block it opened, then its configuration block
  have p1 := popE (c := c) ⟨!k, g₁, w₁⟩ (⟨k, μ, μ⟩ :: C₁) (!k) κ₁ (c * μ) rfl
    (by simp only [pin]; rw [max4 (by linarith) hκ₁ hw₁' le_rfl (Or.inr (Or.inr (Or.inr rfl)))])
  have p2 := popE (c := c) ⟨k, μ, μ⟩ C₁ (!!k) (c * μ) (c * (c * μ)) (by simp)
    (by
      simp only [hC₁, pin]
      rw [max4 hcμ le_rfl hcμ (le_trans hμ1 hcμ) (Or.inr (Or.inl rfl))])
  rw [hk2] at p2
  -- second use of stage s (innermost block of the kernel's type: merged)
  obtain ⟨w₂, g₂, κ₂, hw₂, hw₂', hg₂, hκ₂, d2⟩ :=
    hM.2 0 (⟨k, l, l⟩ :: P) (!k) ν hRν (by linarith)
  have p3 := popE (c := c) ⟨!!k, g₂, w₂⟩ (⟨!k, ν, ν⟩ :: ⟨k, l, l⟩ :: P) (!!k) κ₂ l rfl
    (by
      simp only [pin]
      rw [max4 (by linarith) hκ₂ hw₂' le_rfl (Or.inr (Or.inr (Or.inr rfl))), hcν])
  simp only [Bool.not_not] at p1 p2 p3 d2
  refine ⟨ν, ν, l, hν1, hνl, le_rfl, le_rfl, ?_⟩
  refine d1.trans ((DNW.single p1 (nb _ _ _ _)).trans ((DNW.single p2 ?_).trans
    (d2.trans (DNW.single p3 (nb _ _ _ _)))))
  rw [hC₁]; exact nb _ _ _ _

/-- W13 Claim 2's ratios s_k = S_k/x_k, starting at s₂ = 1 + 1/c. -/
noncomputable def sq (c : ℝ) : ℕ → ℝ
  | 0 => 1 + 1 / c
  | k + 1 => 1 + sq c k ^ 2 / c ^ 3

theorem sq_ge_one {c : ℝ} (hc : 0 < c) : ∀ k, 1 ≤ sq c k
  | 0 => by
    show 1 ≤ 1 + 1 / c
    have : 0 ≤ 1 / c := by positivity
    linarith
  | k + 1 => by
    show 1 ≤ 1 + sq c k ^ 2 / c ^ 3
    have : 0 ≤ sq c k ^ 2 / c ^ 3 := by positivity
    linarith

theorem macE_all {c : ℝ} (hc : 1 ≤ c) : ∀ k, MacE c (sq c k) (c * (c ^ 3) ^ k)
  | 0 => by
    simp only [pow_zero, mul_one]
    exact macE_of_inner hc (sq_ge_one (by linarith) 0) (innerE_base hc le_rfl)
  | k + 1 => by
    have hc0 : 0 < c := by linarith
    have hR : 1 ≤ c * (c ^ 3) ^ k := one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ (one_le_pow₀ hc))
    have h := innerE_step hc hR (sq_ge_one hc0 k) (macE_all hc k)
    rw [show c ^ 3 * (c * (c ^ 3) ^ k) = c * (c ^ 3) ^ (k + 1) by ring] at h
    have hR' : 1 ≤ c * (c ^ 3) ^ (k + 1) :=
      one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ (one_le_pow₀ hc))
    exact macE_of_inner hR' (sq_ge_one hc0 (k + 1)) h

theorem sq_growth {c : ℝ} (hc : 0 < c) : ∀ k : ℕ, 1 + k * (1 - c ^ 3 / 4) ≤ sq c k
  | 0 => by
    simp only [sq, Nat.cast_zero, zero_mul, add_zero]
    have : 0 ≤ 1 / c := by positivity
    linarith
  | k + 1 => by
    have ih := sq_growth hc k
    have hc3 : 0 < c ^ 3 := by positivity
    have key : sq c k - c ^ 3 / 4 ≤ sq c k ^ 2 / c ^ 3 := by
      rw [le_div_iff₀ hc3]; nlinarith [sq_nonneg (sq c k - c ^ 3 / 2)]
    simp only [sq]
    push_cast
    nlinarith

/-- **DvMW in W13's exact calculus:** for every c ∈ [1, ∛4) there is a normal-form proof
NTS[n^a] ⊆ … ⊆ coNTS[n^{a'}], a' ≤ a, using only the exact rules of Lemmas 6.1/6.2. -/
theorem nf_exists {c : ℝ} (hc : 1 ≤ c) (hc3 : c ^ 3 < 4) : ∃ M n, NF (WStepE c) M n := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 < 1 - c ^ 3 / 4 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (c ^ 2 / (1 - c ^ 3 / 4))
  have hs : c ^ 2 ≤ sq c k := by
    have : c ^ 2 < k * (1 - c ^ 3 / 4) := by rwa [div_lt_iff₀ hδ] at hk
    linarith [sq_growth hc0 k]
  set l := c * (c ^ 3) ^ k with hl
  have hl1 : 1 ≤ l := one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ (one_le_pow₀ hc))
  obtain ⟨w, g, κ, hw, hw', hg, hκ, d⟩ :=
    (macE_all hc k).1 [] true l le_rfl rfl (fun u rest he => by simp at he)
  have p1 := popE (c := c) ⟨false, g, w⟩ [⟨true, l, l⟩] false κ (c * l) rfl
    (by simp only [pin]; rw [max4 (by linarith) hκ hw' le_rfl (Or.inr (Or.inr (Or.inr rfl)))])
  have hcl : l ≤ c * l := by nlinarith
  have p2 := popE (c := c) ⟨true, l, l⟩ [] true (c * l) (c * (c * l)) rfl
    (by simp only [pin]; rw [max4 hcl le_rfl hcl (le_trans hl1 hcl) (Or.inr (Or.inl rfl))])
  simp only [Bool.not_true, Bool.not_false] at d p1 p2
  have dd := d.trans (DNW.single p1 (nb _ _ _ _))
  obtain ⟨n, f, h0, hn, hst, hne⟩ := dd.seq
  classical
  let M : ℕ → WLine := fun i => if i ≤ n then f i else ([], false, c * (c * l))
  refine ⟨M, n + 1, by omega, ?_, by simp [M, h0], by simp [M, h0], by simp [M], by simp [M],
    ?_, ?_⟩
  · intro i hi
    by_cases h : i + 1 ≤ n
    · simp only [M, show i ≤ n by omega, h, if_true]; exact hst i (by omega)
    · have : i = n := by omega
      subst this
      simp only [M, le_refl, if_true, h, if_false]; rw [hn]; exact p2
  · intro i h1 h2
    simp only [M, show i ≤ n by omega, if_true]
    exact hne i h1 (by omega)
  · simp only [M, show ¬ n + 1 ≤ n by omega, if_false, Nat.zero_le, if_true, h0]
    show c * (c * l) ≤ sq c k * l
    have : c * (c * l) = c ^ 2 * l := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hs (by linarith)

/-- **Threshold of W13's literal TAUT calculus (c ≥ 1): normal-form proofs exist iff c³ < 4.**
Both directions kernel-checked: `nf_exists` (exact rules) and `TW.no_nf` (LP relaxation, which
contains the exact rules). -/
theorem threshold_literal {c : ℝ} (hc : 1 ≤ c) :
    (∃ M n, NF (WStepE c) M n) ↔ c ^ 3 < 4 := by
  constructor
  · rintro ⟨M, n, hn, hp, h0, ht0, hN, htN, hmid, hle⟩
    by_contra h'
    push Not at h'
    exact no_nf h' M n ⟨hn, fun i hi => wstepE_wstep (hp i hi), h0, ht0, hN, htN, hmid, hle⟩
  · exact nf_exists hc

end TDL
end PastaMath.TautThreshold
