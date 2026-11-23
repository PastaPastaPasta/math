-- SPDX-License-Identifier: Apache-2.0
import PastaMath.TautThreshold.Limit

/-!
The Diehl–van Melkebeek–Williams family (W13 Theorem 6.7, Claims 1–2) as a Lean
construction in the reduced TAUT calculus `TL.TStep`: for every c with 1 ≤ c and c³ < 4 there is
a refutation. With `TL.no_trefutation` this makes the threshold of `TStep` exactly ∛4 in Lean
(`threshold`).

Reduced form of DvMW's stage k (`Mac c s`): in any context whose innermost superscript is 0,
NTS[n^{s·λ}] derives (∃ n^λ)^λ(∀ n^λ)^λ coNTS[n^λ] (both when the kernel is opposite to the
innermost block, opening two blocks, and when it matches, merging). Stage k+1 uses stage k twice
(once opposite, once matching), so s ↦ 1 + s²/c³ (W13 Claim 2). Since
1 + s²/c³ − s ≥ 1 − c³/4 > 0, s grows at least linearly, and once s > c² two pops refute.
-/

namespace PastaMath.TautThreshold
namespace TD

open TL

/-- Derivations whose lines after the first have a nonempty block list. -/
inductive DNE (c : ℝ) : TLine → TLine → Prop
  | refl (L : TLine) : DNE c L L
  | tail {L M N : TLine} : DNE c L M → TStep c M N → N.1 ≠ [] → DNE c L N

theorem DNE.trans {c : ℝ} {L M N : TLine} (h1 : DNE c L M) (h2 : DNE c M N) : DNE c L N := by
  induction h2 with
  | refl => exact h1
  | tail _ hs hn ih => exact DNE.tail ih hs hn

theorem DNE.single {c : ℝ} {L M : TLine} (h : TStep c L M) (hM : M.1 ≠ []) : DNE c L M :=
  DNE.tail (DNE.refl L) h hM

theorem DNE.seq {c : ℝ} {L M : TLine} (h : DNE c L M) :
    ∃ (n : ℕ) (f : ℕ → TLine), f 0 = L ∧ f n = M ∧ (∀ i < n, TStep c (f i) (f (i + 1))) ∧
      (∀ i, 0 < i → i ≤ n → (f i).1 ≠ []) := by
  induction h with
  | refl => exact ⟨0, fun _ => L, rfl, rfl, fun i hi => absurd hi (by omega), fun i h1 h2 => absurd h1 (by omega)⟩
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

/-- A derivation NTS[n^{a₀}] → (virtual block) ⊢* M, followed by a pop to a quantifier-free line
at exponent ≤ a₀, is a `TRefutes` instance. -/
theorem trefutes_of {c a₀ e : ℝ} {M : TLine} (ha : 0 < a₀) (hd : DNE c ([0], true, a₀) M)
    (hpop : TStep c M ([], true, e)) (he : e ≤ a₀) : ∃ n T, TRefutes c n T := by
  obtain ⟨n, f, h0, hn, hst, hne⟩ := hd.seq
  classical
  let T : ℕ → TLine := fun i =>
    match i with
    | 0 => ([], true, a₀)
    | j + 1 => if j ≤ n then f j else ([], true, e)
  refine ⟨n + 2, T, by omega, rfl, ?_, ha, ?_, ?_, ?_⟩
  · show (if n + 1 ≤ n then f (n + 1) else ([], true, e)).1 = []
    simp
  · show (if n + 1 ≤ n then f (n + 1) else ([], true, e)).2.2 ≤ a₀
    simp [he]
  · intro i hi
    match i, hi with
    | 0, _ =>
      show TStep c ([], true, a₀) (if 0 ≤ n then f 0 else ([], true, e))
      simp only [Nat.zero_le, if_true, h0]; exact TStep.init a₀
    | j + 1, hj =>
      show TStep c (if j ≤ n then f j else ([], true, e)) (if j + 1 ≤ n then f (j + 1) else ([], true, e))
      by_cases h : j + 1 ≤ n
      · simp only [show j ≤ n by omega, h, if_true]; exact hst j (by omega)
      · have : j = n := by omega
        subst this
        simp only [le_refl, if_true, h, if_false]; rw [hn]; exact hpop
  · intro i h1 h2
    match i, h1, h2 with
    | j + 1, _, hj =>
      show (if j ≤ n then f j else ([], true, e)).1 ≠ []
      simp only [show j ≤ n by omega, if_true]
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; rw [h0]; simp
      · exact hne j hj0 (by omega)

theorem ts {c : ℝ} {l1 l2 m1 m2 : List ℝ} {t t' : Bool} {a a' : ℝ} (h : TStep c (l1, t, a) (l2, t', a'))
    (e1 : l1 = m1) (e2 : l2 = m2) : TStep c (m1, t, a) (m2, t', a') := by
  subst e1 e2; exact h

theorem weak_last {c : ℝ} (bs : List ℝ) (u v a a' : ℝ) (t : Bool) (huv : u ≤ v) (ha : a ≤ a') :
    TStep c (bs ++ [u], t, a) (bs ++ [v], t, a') := by
  refine TStep.weak _ _ t a a' (by simp) ?_ ha
  intro i
  rcases lt_or_ge i bs.length with h | h
  · rw [getD_lt h, getD_lt h]
  · rw [List.getD_append_right _ _ _ _ h, List.getD_append_right _ _ _ _ h]
    rcases Nat.eq_zero_or_pos (i - bs.length) with h0 | h0
    · rw [h0]; simpa using huv
    · obtain ⟨m, hm⟩ : ∃ m, i - bs.length = m + 1 := ⟨i - bs.length - 1, by omega⟩
      rw [hm]; simp

theorem ne_nil_app (Q l : List ℝ) (hl : l ≠ []) : Q ++ l ≠ [] := by simp [hl]

/-- Reduced stage statement with ratio s = S_k / x_k (scale λ = x_k). -/
def Mac (c s : ℝ) : Prop :=
  ∀ (P : List ℝ) (l : ℝ), 0 ≤ l →
    DNE c (P ++ [0], false, s * l) (P ++ [0, l, l], true, l) ∧
      DNE c (P ++ [0], true, s * l) (P ++ [l, l], true, l)

/-- What remains of a stage after its first speedup. -/
def Inner (c s : ℝ) : Prop :=
  ∀ (Q : List ℝ) (l : ℝ), 0 ≤ l → DNE c (Q ++ [l, 0], false, s * l - l) (Q ++ [l, l], true, l)

theorem mac_of_inner {c s : ℝ} (hs : 1 ≤ s) (hI : Inner c s) : Mac c s := by
  intro P l hl
  have hxa : l ≤ s * l := by nlinarith
  constructor
  · have h1 := TStep.speedO (c := c) (t := false) P 0 (s * l) l l 0 (s * l - l) hl hxa
      (by rw [max_eq_left hl]) le_rfl le_rfl
    have h1' : TStep c (P ++ [0], false, s * l) ((P ++ [0]) ++ [l, 0], false, s * l - l) :=
      ts h1 rfl (by simp)
    have h2 := hI (P ++ [0]) l hl
    have := (DNE.single h1' (by simp)).trans h2
    simpa using this
  · have h1 := TStep.speedM (c := c) P 0 (s * l) l l 0 (s * l - l) hl hxa
      (by rw [max_eq_left hl]) le_rfl le_rfl
    exact (DNE.single h1 (by simp)).trans (hI P l hl)

theorem inner_one (c : ℝ) : Inner c 1 := by
  intro Q l hl
  have h1 := TStep.flip (c := c) (Q ++ [l]) 0 (1 * l - l) 0 false (by simp)
  have h1' : TStep c (Q ++ [l, 0], false, 1 * l - l) (Q ++ [l, 0], true, 0) := ts h1 (by simp) (by simp)
  have h2 := weak_last (c := c) (Q ++ [l]) 0 l 0 l true hl hl
  have h2' : TStep c (Q ++ [l, 0], true, 0) (Q ++ [l, l], true, l) := ts h2 (by simp) (by simp)
  exact (DNE.single h1' (by simp)).trans (DNE.single h2' (by simp))

/-- **DvMW stage step (W13 Claim 1 / Claim 2):** stage s gives stage 1 + s²/c³, applying the
previous stage twice. -/
theorem inner_step {c s : ℝ} (hc : 1 ≤ c) (hs : 1 ≤ s) (hM : Mac c s) :
    Inner c (1 + s ^ 2 / c ^ 3) := by
  intro Q l hl
  have hc0 : 0 < c := by linarith
  have hc3 : 0 < c ^ 3 := by positivity
  set μ := s * l / c ^ 3 with hμ
  set ν := l / c with hν
  have hμ0 : 0 ≤ μ := by positivity
  have hν0 : 0 ≤ ν := by positivity
  have hk : (1 + s ^ 2 / c ^ 3) * l - l = s * μ := by rw [hμ]; ring
  have hk2 : c * (c * μ) = s * ν := by rw [hμ, hν]; field_simp
  have hcν : c * ν = l := by rw [hν]; field_simp
  have hνl : ν ≤ l := by rw [hν, div_le_iff₀ hc0]; nlinarith
  rw [hk]
  -- first use of the previous stage (kernel opposite)
  have d1 := (hM (Q ++ [l]) μ hμ0).1
  simp only [List.append_assoc, List.cons_append, List.nil_append] at d1
  -- pop the index block, then the configuration block
  have p1 := TStep.pop (c := c) (t := true) (Q ++ [l, 0, μ]) μ μ (c * μ)
    (by rw [show Q ++ [l, 0, μ] = (Q ++ [l, 0]) ++ [μ] by simp, top_concat, max_self, max_self])
  have p1' : TStep c (Q ++ [l, 0, μ, μ], true, μ) (Q ++ [l, 0, μ], true, c * μ) :=
    ts p1 (by simp) rfl
  have hcμ : μ ≤ c * μ := by nlinarith
  have p2 := TStep.pop (c := c) (t := true) (Q ++ [l, 0]) μ (c * μ) (c * (c * μ))
    (by rw [show Q ++ [l, 0] = (Q ++ [l]) ++ [0] by simp, top_concat, max_eq_right hcμ,
          max_eq_right (by linarith)])
  have p2' : TStep c (Q ++ [l, 0, μ], true, c * μ) (Q ++ [l, 0], true, s * ν) := by
    rw [← hk2]; exact ts p2 (by simp) rfl
  -- second use of the previous stage (kernel matches the index block: merged)
  have d2 := (hM (Q ++ [l]) ν hν0).2
  simp only [List.append_assoc, List.cons_append, List.nil_append] at d2
  have p3 := TStep.pop (c := c) (t := true) (Q ++ [l, ν]) ν ν l
    (by rw [show Q ++ [l, ν] = (Q ++ [l]) ++ [ν] by simp, top_concat, max_self, max_self, hcν])
  have p3' : TStep c (Q ++ [l, ν, ν], true, ν) (Q ++ [l, ν], true, l) := ts p3 (by simp) rfl
  have w := weak_last (c := c) (Q ++ [l]) ν l l l true hνl le_rfl
  have w' : TStep c (Q ++ [l, ν], true, l) (Q ++ [l, l], true, l) := ts w (by simp) (by simp)
  exact d1.trans ((DNE.single p1' (by simp)).trans ((DNE.single p2' (by simp)).trans
    (d2.trans ((DNE.single p3' (by simp)).trans (DNE.single w' (by simp))))))

/-- DvMW's ratio sequence s_k = S_k / x_k (W13 Claim 2), started at s = 1. -/
noncomputable def sq (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => 1 + sq c k ^ 2 / c ^ 3

theorem sq_ge_one {c : ℝ} (hc : 0 < c) : ∀ k, 1 ≤ sq c k
  | 0 => le_rfl
  | k + 1 => by
    show 1 ≤ 1 + sq c k ^ 2 / c ^ 3
    have : 0 ≤ sq c k ^ 2 / c ^ 3 := by positivity
    linarith

theorem mac_all {c : ℝ} (hc : 1 ≤ c) : ∀ k, Mac c (sq c k)
  | 0 => mac_of_inner le_rfl (inner_one c)
  | k + 1 => by
    have hs := sq_ge_one (by linarith : (0 : ℝ) < c) k
    exact mac_of_inner (sq_ge_one (by linarith) (k + 1)) (inner_step hc hs (mac_all hc k))

/-- Below ∛4 the ratio grows at least linearly: s_{k+1} ≥ s_k + (1 − c³/4). -/
theorem sq_growth {c : ℝ} (hc : 0 < c) : ∀ k : ℕ, 1 + k * (1 - c ^ 3 / 4) ≤ sq c k
  | 0 => by simp [sq]
  | k + 1 => by
    have ih := sq_growth hc k
    have hc3 : 0 < c ^ 3 := by positivity
    have key : sq c k - c ^ 3 / 4 ≤ sq c k ^ 2 / c ^ 3 := by
      rw [le_div_iff₀ hc3]; nlinarith [sq_nonneg (sq c k - c ^ 3 / 2)]
    simp only [sq]
    push_cast
    nlinarith

/-- **DvMW (W13 Theorem 6.7) in the reduced calculus:** a refutation for every c ∈ [1, ∛4). -/
theorem dvmw {c : ℝ} (hc : 1 ≤ c) (hc3 : c ^ 3 < 4) : ∃ n L, TRefutes c n L := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 < 1 - c ^ 3 / 4 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (c ^ 2 / (1 - c ^ 3 / 4))
  have hgrow := sq_growth hc0 k
  have hs : c ^ 2 < sq c k := by
    have : c ^ 2 < k * (1 - c ^ 3 / 4) := by rwa [div_lt_iff₀ hδ] at hk
    linarith
  have hd := (mac_all hc k [] 1 zero_le_one).2
  simp only [List.nil_append, mul_one] at hd
  have p1 := TStep.pop (c := c) (t := true) [1] 1 1 c (by simp [top])
  have p1' : TStep c ([1, 1], true, 1) ([1], true, c) := ts p1 (by simp) rfl
  have p2 := TStep.pop (c := c) (t := true) [] 1 c (c * c)
    (by rw [show top ([] : List ℝ) = 0 from rfl, max_eq_right hc, max_eq_right (by linarith)])
  have p2' : TStep c ([1], true, c) ([], true, c * c) := ts p2 (by simp) rfl
  exact trefutes_of (lt_of_le_of_lt (sq_nonneg c) hs) (hd.trans (DNE.single p1' (by simp))) p2'
    (by nlinarith)

/-- **The threshold of the reduced TAUT calculus is exactly ∛4** (for c ≥ 1): both directions
kernel-checked (`TL.no_trefutation` and `dvmw`). -/
theorem threshold {c : ℝ} (hc : 1 ≤ c) : (∃ n L, TRefutes c n L) ↔ c ^ 3 < 4 := by
  constructor
  · rintro ⟨n, L, h⟩
    by_contra h'
    push Not at h'
    exact no_trefutation h' n L h
  · exact dvmw hc

end TD
end PastaMath.TautThreshold
