-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Ceiling
import PastaMath.OneTapeThreshold.Displays

/-!
# Two moves outside the formal calculus

* `HY.Incl`: the inclusion DTIME_d[t] ⊆ DTISP[t, t] under any prefix, from `(bl, T a)` to
  `(bl, S a a)` (a machine running for time t visits at most t cells). Lemma 3.4 with e = c applied
  to a level is Lemma 7.2 (`HY.Step.slow`) followed by this inclusion. Its relaxed form is
  `HL.Widen`: from `(bl, T a)` to `(bl, S a₂ e₂)` with a ≤ a₂ and a ≤ e₂, which also covers
  Lemma 3.4 with time exponent c' ≥ c and space exponent e ≥ c (below).
* `HY.SpeedLog`: Lemma 3.3 in a prefix as in `HY.Step.speedMerge` and `HY.Step.speedNew`, except
  that the new log n block gets an arbitrary output superscript ℓ ≥ 0 (for example 1 or max(b, 1), as
  displayed in Williams's sketch of Theorem 7.9, instead of max(b, e)). It keeps the guess exponent of
  Lemma 3.3. Its relaxed form is `HL.Loose` (relaxed lines have no guess exponents).

`HL.widen_dec`: for c ≥ 0 and d ≥ 1, a `Widen` step from `(bl, T a)` with a ≥ 0 followed by an
`RStep` from the `S` line can be replaced by Lemma 7.1 with s = a/d (`convM` or `convN`) followed by an
`RStep` to the same line (`HL.widen_dec_W`: the same with `Loose` steps allowed). `HL.path_unwiden`:
if a relation R preserves `NN` (all entries ≥ 0) and satisfies the conclusion of `widen_dec`, then a
path of R and `Widen` steps from a line with `NN` to a line with a `T` kernel can be replaced by an
R-path of the same length with the same two endpoints. For `RStep c d` with c ≥ 0 and d ≥ 1 this is
`HL.rpath_of_rpathX`. So a statement about `RPath` that depends only on the length and the two
endpoints of a path transfers to `RPathX`; a statement about the intermediate lines need not: from
`([], T 1)` a `Widen` step reaches `([], S 1 1)`, which lowers the one-level potential from 1 to 0.

Lemma 3.4 needs NTIME[n] ⊆ DTISP[n^{c'}, n^e]. From NTIME[n] ⊆ DTIME_d[n^c] this follows for every
c' ≥ c and e ≥ c (the best case being c' = e = c), and for no e < c by any argument we know. Lemma 3.4
is read here inside a prefix, with the maximum m of the Slowdown Rule of Williams's §4 (Definition 4.1)
and of Lemma 7.2, which includes the output b_k of the remaining prefix; the statement of §3 alone is for
one block over a DTIME kernel and has the three-term maximum max{a, a', b}. Read so, each application of
Lemma 3.4 gives the line of `HY.Step.slow` followed by a `Widen` step (time and space c'·m, e·m ≥ c·m,
where c·m is the time exponent `slow` gives); `HY.Incl` is the case c' = e = c. So the weakened forms
are covered by part (1) of `HLM.ceilingX_d{1,2,3}` (relaxed, `HL.RPathX`) and the exact form also by
part (2).

The ceilings are theorems about the formalised rule set (`HY.Step` with the extensions named in each
theorem), which is our reading of Williams's lemmas as set out in Section 2.4 of the paper. His proof
sketches display some lines that differ from it, and for some of those the ceilings are not established;
the scope table at the end of Section 2.4 is the full statement (not claimed exhaustive).

* `HLM.ceilingX_d1`, `ceilingX_d2`, `ceilingX_d3`: for every real c ≥ 6547/5000, 149/125, 712/625
  respectively, (1) there is no path of `RStep c d` and `Widen` steps (`HL.RPathX`) with n ≥ 1 from
  `([], T a₀)`, a₀ > 0, to `([], T a')` with a' ≤ a₀, and (2) every path of `HY.Step c d` and
  `HY.Incl` steps of length n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` has a₀ < a'.
* `HY.path_alt_incl`: along a path of `HY.Step` and `HY.Incl` steps from `([], T a₀)` every line
  alternates (`HY.step_alt` in `Displays.lean`; `HY.Incl` keeps the prefix).
* `HL.qf_ge_W`: under `Facts c d g` and d ≥ 1, along every `RPathW c d` (`RStep`, `Loose` and
  `Widen` steps) from `([], T a₀)`, a₀ ≥ 0, to `([], T a')`, a₀ ≤ a'. `HL.no_drop_W`: for d ≥ 1,
  c ≥ 1 and c² ≥ 1 + 1/d, the same along every path of `HY.Step c d`, `HY.Incl` and `HY.SpeedLog`
  steps. This excludes a' < a₀ (so strict normal forms), not a path with a' = a₀. The one-level potential does not use the output
  superscript of the new log n block (`HL.speed_ineq`). The multi-level potentials do, so the
  ceilings `HLM.ceiling_d*` are not extended to `HY.SpeedLog`.
* `HL.stepO_cases`, `HL.no_nfO`: if ℓ o e ≥ 0 for o ≥ 1, e ≥ 0 (e.g. under `HY.LogOK ℓ`), every
  `HY.StepO ℓ` step is a `HY.Step` or `HY.SpeedLog` step, so for d ≥ 1, c ≥ 1 and c² ≥ 1 + 1/d there is
  no `HY.NFO ℓ c d M n`.
* `HL.rpathW_last_T`: for c ≥ 0, an `RPathW c d` path of length ≥ 1 ending at `(P, T a')` has
  c · pin P ≤ a' (only `RStep.slow` produces a `T` kernel). So a slowdown to a time below c · pin P under
  the retained prefix P is not reached by any derivation in these rule sets.
* `HY.NFX`: the strict normal form for `HY.Step` and `HY.Incl` steps (used by `threshold_sup`).
-/

namespace PastaMath.OneTapeThreshold

namespace HY

/-- The inclusion DTIME_d[n^a] ⊆ DTISP[n^a, n^a] under the prefix `bl`. -/
inductive Incl : Line → Line → Prop
  | mk (bl : List Blk) (a : ℝ) : Incl (bl, .T a) (bl, .S a a)

/-- Lemma 3.3 in a prefix (Speedup Rules 1 and 2) with the side conditions of `Step.speedMerge` and
`Step.speedNew`, but with an arbitrary output superscript ℓ ≥ 0 for the new log n block. -/
inductive SpeedLog : Line → Line → Prop
  | merge (u : Blk) (rest : List Blk) (a e x ℓ : ℝ) (ha : 1 ≤ a) (he : 0 ≤ e)
      (hex : e ≤ a - x) (hx : 0 ≤ x) (hx1 : x ≤ a - 1) (hb : 1 ≤ u.o) (hℓ : 0 ≤ ℓ) :
      SpeedLog (u :: rest, .S a e)
        (⟨!u.q, 0, ℓ⟩ :: ⟨u.q, max u.g (x + e), max u.o (x + e)⟩ :: rest, .S (a - x) e)
  | new (bl : List Blk) (q : Bool) (a e x ℓ : ℝ) (hq : ∀ u rest, bl = u :: rest → u.q ≠ q)
      (ha : 1 ≤ a) (he : 0 ≤ e) (hex : e ≤ a - x) (hx : 0 ≤ x) (hx1 : x ≤ a - 1)
      (hb : 1 ≤ pin bl) (hℓ : 0 ≤ ℓ) :
      SpeedLog (bl, .S a e) (⟨!q, 0, ℓ⟩ :: ⟨q, x + e, max (pin bl) (x + e)⟩ :: bl, .S (a - x) e)

theorem incl_alt {L L' : Line} (h : Incl L L') (hA : Alt L.1) : Alt L'.1 := by
  cases h
  exact hA

/-- Along a path of `Step c d` and `Incl` steps from `([], T a₀)` every line alternates. -/
theorem path_alt_incl {c d a₀ : ℝ} {M : ℕ → Line} {n : ℕ}
    (hp : ∀ i < n, Step c d (M i) (M (i + 1)) ∨ Incl (M i) (M (i + 1)))
    (h0 : M 0 = ([], .T a₀)) : ∀ i ≤ n, Alt (M i).1 := by
  intro i hi
  induction i with
  | zero => rw [h0]; trivial
  | succ j ih =>
    rcases hp j (by omega) with h | h
    · exact step_alt h (ih (by omega))
    · exact incl_alt h (ih (by omega))

/-- `NF` for the calculus `HY.Step c d` with the inclusion `HY.Incl` added: the same conditions, with
every step a `Step c d` or an `Incl` step. -/
def NFX (c d : ℝ) (M : ℕ → Line) (n : ℕ) : Prop :=
  1 ≤ n ∧ (∀ i < n, Step c d (M i) (M (i + 1)) ∨ Incl (M i) (M (i + 1))) ∧
    (∃ a, M 0 = ([], .T a)) ∧ (∃ a', M n = ([], .T a')) ∧
    (∀ i, 0 < i → i < n → (M i).1 ≠ []) ∧ 1 ≤ (M n).2.time ∧ (M n).2.time < (M 0).2.time ∧
    ∀ i ≤ n, Alt (M i).1

theorem nfX_of_nf {c d : ℝ} {M : ℕ → Line} {n : ℕ} (h : NF c d M n) : NFX c d M n :=
  ⟨h.1, fun i hi => Or.inl (h.2.1 i hi), h.2.2⟩

end HY

namespace HL

/-- The relaxed inclusion: from `(bl, T a)` to `(bl, S a₂ e₂)` with a ≤ a₂ and a ≤ e₂. -/
def Widen (L L' : RLine) : Prop :=
  ∃ bl a a₂ e₂, L = (bl, .T a) ∧ L' = (bl, .S a₂ e₂) ∧ a ≤ a₂ ∧ a ≤ e₂

/-- Relaxed Lemma 3.3 in which the new log n block has any output superscript ≥ 0: `speedM` and
`speedN` of `RStep` with the lower bound max(b, e) (resp. max(pin bl, e)) on that block replaced
by 0. -/
inductive Loose : RLine → RLine → Prop
  | speedM (b : ℝ) (rest : List ℝ) (a e x b' L a₂ e₂ : ℝ) (hx : 0 ≤ x) (hex : e ≤ a - x)
      (h' : max b (x + e) ≤ b') (hL : 0 ≤ L) (ha : a - x ≤ a₂) (he : e ≤ e₂) :
      Loose (b :: rest, .S a e) (L :: b' :: rest, .S a₂ e₂)
  | speedN (bl : List ℝ) (a e x g₁ g₂ a₂ e₂ : ℝ) (hx : 0 ≤ x) (hex : e ≤ a - x)
      (h₁ : max (pin bl) (x + e) ≤ g₁) (h₂ : 0 ≤ g₂) (ha : a - x ≤ a₂) (he : e ≤ e₂) :
      Loose (bl, .S a e) (g₂ :: g₁ :: bl, .S a₂ e₂)

/-- `M 0, …, M n` is a path of `RStep c d` and `Widen` steps. -/
def RPathX (c d : ℝ) (M : ℕ → RLine) (n : ℕ) : Prop :=
  ∀ i < n, RStep c d (M i) (M (i + 1)) ∨ Widen (M i) (M (i + 1))

/-- `M 0, …, M n` is a path of `RStep c d`, `Loose` and `Widen` steps. -/
def RPathW (c d : ℝ) (M : ℕ → RLine) (n : ℕ) : Prop :=
  ∀ i < n, (RStep c d (M i) (M (i + 1)) ∨ Loose (M i) (M (i + 1))) ∨ Widen (M i) (M (i + 1))

theorem nn_widen {L L' : RLine} (h : Widen L L') (hL : NN L) : NN L' := by
  obtain ⟨bl, a, a₂, e₂, rfl, rfl, ha, he⟩ := h
  obtain ⟨hb, hk⟩ := hL
  simp only [KNN] at hk
  exact ⟨hb, by simp only [KNN]; exact ⟨by linarith, by linarith⟩⟩

theorem nn_loose {L L' : RLine} (h : Loose L L') (hL : NN L) : NN L' := by
  obtain ⟨hb, hk⟩ := hL
  cases h with
  | speedM b rest a e x b' L a₂ e₂ hx hex h' hL ha he =>
    simp only [KNN] at hk
    obtain ⟨_, hk2⟩ := hk
    have hb0 : 0 ≤ b := hb b (by simp)
    refine ⟨?_, ?_, ?_⟩
    · intro y hy; simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact hL
      · exact le_trans (le_trans hb0 (le_max_left _ _)) h'
      · exact hb y (by simp [hy])
    · linarith
    · linarith
  | speedN bl a e x g₁ g₂ a₂ e₂ hx hex h₁ h₂ ha he =>
    simp only [KNN] at hk
    obtain ⟨_, hk2⟩ := hk
    have hp : 0 ≤ pin bl := by
      cases bl with
      | nil => simp [pin]
      | cons u _ => exact hb u (by simp)
    refine ⟨?_, ?_, ?_⟩
    · intro y hy; simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact h₂
      · exact le_trans (le_trans hp (le_max_left _ _)) h₁
      · exact hb y hy
    · linarith
    · linarith

/-- For c ≥ 0 and d ≥ 1: if a ≥ 0, a ≤ a₂, a ≤ e₂ and `RStep c d (bl, S a₂ e₂) L₃`, then there is
`L'` with `RStep c d (bl, T a) L'` (Lemma 7.1 with s = a/d) and `RStep c d L' L₃`. -/
theorem widen_dec {c d : ℝ} (hc : 0 ≤ c) (hd : 1 ≤ d) {bl : List ℝ} {a a₂ e₂ : ℝ} {L₃ : RLine}
    (ha0 : 0 ≤ a) (ha : a ≤ a₂) (he : a ≤ e₂) (h : RStep c d (bl, .S a₂ e₂) L₃) :
    ∃ L', RStep c d (bl, .T a) L' ∧ RStep c d L' L₃ := by
  have hd0 : 0 < d := by linarith
  have hs0 : 0 ≤ a / d := div_nonneg ha0 hd0.le
  have hsa : a / d ≤ a := div_le_self ha0 hd
  have hds : d * (a / d) ≤ e₂ := by rw [mul_div_cancel₀ a hd0.ne']; exact he
  have ht : a - a / d ≤ e₂ := by linarith
  cases h with
  | speedM b rest a₂ e₂ x b' L a₃ e₃ hx hex h' hL ha' he' =>
    refine ⟨_, RStep.convM b rest a (a / d) _ a₂ e₂ hs0 hsa le_rfl ha hds, ?_⟩
    have hxe : x + e₂ ≤ b' := le_trans (le_max_right _ _) h'
    have heL : e₂ ≤ L := le_trans (le_max_right _ _) hL
    refine RStep.speedM _ rest a₂ e₂ x b' L a₃ e₃ hx hex ?_ ?_ ha' he'
    · exact max_le (max_le (le_trans (le_max_left _ _) h') (by linarith)) hxe
    · exact max_le (max_le (le_trans (le_max_left _ _) hL) (by linarith)) heL
  | speedN bl a₂ e₂ x g₁ g₂ a₃ e₃ hx hex h₁ h₂ ha' he' =>
    refine ⟨_, RStep.convN bl a (a / d) _ a₂ e₂ hs0 hsa le_rfl ha hds, ?_⟩
    have hxe : x + e₂ ≤ g₁ := le_trans (le_max_right _ _) h₁
    have heL : e₂ ≤ g₂ := le_trans (le_max_right _ _) h₂
    refine RStep.speedM _ bl a₂ e₂ x g₁ g₂ a₃ e₃ hx hex ?_ ?_ ha' he'
    · exact max_le (max_le (le_trans (le_max_left _ _) h₁) (by linarith)) hxe
    · exact max_le (max_le (le_trans (le_max_left _ _) h₂) (by linarith)) heL
  | slow b rest k a' hh =>
    refine ⟨_, RStep.convM b rest a (a / d) _ a₂ e₂ hs0 hsa le_rfl ha hds, ?_⟩
    refine RStep.slow _ rest (.S a₂ e₂) a' (le_trans ?_ hh)
    apply mul_le_mul_of_nonneg_left _ hc
    simp only [HK.time]
    refine max_le (max_le (le_max_of_le_left (le_max_left _ _)) ?_) (le_max_right _ _)
    refine max_le (le_max_of_le_left (le_max_right _ _)) (le_max_of_le_right ?_)
    linarith

/-- `widen_dec` with `Loose` steps allowed: for c ≥ 0 and d ≥ 1, if a ≥ 0, a ≤ a₂, a ≤ e₂ and
`(bl, S a₂ e₂)` steps to `L₃` by `RStep c d` or `Loose`, then `(bl, T a)` steps by `RStep c d` or `Loose`
to some `L'` that steps to `L₃` by `RStep c d` or `Loose`. (The proof always takes the first step to be
an `RStep`, Lemma 7.1 with s = a/d; the statement records only the disjunction.) -/
theorem widen_dec_W {c d : ℝ} (hc : 0 ≤ c) (hd : 1 ≤ d) {bl : List ℝ} {a a₂ e₂ : ℝ} {L₃ : RLine}
    (ha0 : 0 ≤ a) (ha : a ≤ a₂) (he : a ≤ e₂)
    (h : RStep c d (bl, .S a₂ e₂) L₃ ∨ Loose (bl, .S a₂ e₂) L₃) :
    ∃ L', (RStep c d (bl, .T a) L' ∨ Loose (bl, .T a) L') ∧ (RStep c d L' L₃ ∨ Loose L' L₃) := by
  rcases h with h | h
  · obtain ⟨L', h1, h2⟩ := widen_dec hc hd ha0 ha he h
    exact ⟨L', Or.inl h1, Or.inl h2⟩
  have hd0 : 0 < d := by linarith
  have hs0 : 0 ≤ a / d := div_nonneg ha0 hd0.le
  have hsa : a / d ≤ a := div_le_self ha0 hd
  have hds : d * (a / d) ≤ e₂ := by rw [mul_div_cancel₀ a hd0.ne']; exact he
  have ht : a - a / d ≤ e₂ := by linarith
  cases h with
  | speedM b rest a₂ e₂ x b' L a₃ e₃ hx hex h' hL ha' he' =>
    refine ⟨_, Or.inl (RStep.convM b rest a (a / d) _ a₂ e₂ hs0 hsa le_rfl ha hds), Or.inr ?_⟩
    have hxe : x + e₂ ≤ b' := le_trans (le_max_right _ _) h'
    refine Loose.speedM _ rest a₂ e₂ x b' L a₃ e₃ hx hex ?_ hL ha' he'
    exact max_le (max_le (le_trans (le_max_left _ _) h') (by linarith)) hxe
  | speedN bl a₂ e₂ x g₁ g₂ a₃ e₃ hx hex h₁ h₂ ha' he' =>
    refine ⟨_, Or.inl (RStep.convN bl a (a / d) _ a₂ e₂ hs0 hsa le_rfl ha hds), Or.inr ?_⟩
    have hxe : x + e₂ ≤ g₁ := le_trans (le_max_right _ _) h₁
    refine Loose.speedM _ bl a₂ e₂ x g₁ g₂ a₃ e₃ hx hex ?_ h₂ ha' he'
    exact max_le (max_le (le_trans (le_max_left _ _) h₁) (by linarith)) hxe

/-- Removing `Widen` steps from a path. Let `R` preserve `NN` and satisfy the conclusion of
`widen_dec` (with a ≥ 0). If `M 0, …, M n` is a path of `R` and `Widen` steps, `NN (M 0)`, and
`M n` has a `T` kernel, there is an `R`-path `M' 0, …, M' n` with `M' 0 = M 0` and `M' n = M n`. -/
theorem path_unwiden {R : RLine → RLine → Prop} (hnn : ∀ {L L' : RLine}, R L L' → NN L → NN L')
    (hdec : ∀ {bl : List ℝ} {a a₂ e₂ : ℝ} {L₃ : RLine}, 0 ≤ a → a ≤ a₂ → a ≤ e₂ →
      R (bl, .S a₂ e₂) L₃ → ∃ L', R (bl, .T a) L' ∧ R L' L₃)
    {M : ℕ → RLine} {n : ℕ} (hp : ∀ i < n, R (M i) (M (i + 1)) ∨ Widen (M i) (M (i + 1)))
    (h0 : NN (M 0)) {bl : List ℝ} {a' : ℝ} (hN : M n = (bl, .T a')) :
    ∃ M' : ℕ → RLine, (∀ i < n, R (M' i) (M' (i + 1))) ∧ M' 0 = M 0 ∧ M' n = M n := by
  classical
  have hnnM : ∀ i ≤ n, NN (M i) := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ j ih =>
      intro hj
      rcases hp j (by omega) with h | h
      · exact hnn h (ih (by omega))
      · exact nn_widen h (ih (by omega))
  have noWW : ∀ {L₁ L₂ L₃ : RLine}, Widen L₁ L₂ → ¬ Widen L₂ L₃ := by
    rintro L₁ L₂ L₃ ⟨_, _, _, _, _, h2, _, _⟩ ⟨_, _, _, _, h1, _, _, _⟩
    rw [h2] at h1; cases h1
  have key : ∀ i, ∃ L', i < n ∧ Widen (M i) (M (i + 1)) → R (M i) L' ∧ R L' (M (i + 2)) := by
    intro i
    by_cases hc : i < n ∧ Widen (M i) (M (i + 1))
    · obtain ⟨hi, hw⟩ := hc
      have hi1 : i + 1 < n := by
        by_contra hge
        have hin : i + 1 = n := by omega
        obtain ⟨_, _, _, _, _, h2, _, _⟩ := hw
        rw [hin, hN] at h2; cases h2
      have hR : R (M (i + 1)) (M (i + 2)) := (hp (i + 1) hi1).resolve_right (noWW hw)
      obtain ⟨bl', a, a₂, e₂, h1, h2, ha, he⟩ := hw
      have ha0 : 0 ≤ a := by
        have := (hnnM i hi.le).2; rw [h1] at this; exact this
      rw [h2] at hR
      obtain ⟨L', hL1, hL2⟩ := hdec ha0 ha he hR
      exact ⟨L', fun _ => ⟨h1 ▸ hL1, hL2⟩⟩
    · exact ⟨M i, fun h => absurd h hc⟩
  choose f hf using key
  let M' : ℕ → RLine := fun j => match j with
    | 0 => M 0
    | i + 1 => if i < n ∧ Widen (M i) (M (i + 1)) then f i else M (i + 1)
  have hpos : ∀ i, i < n ∧ Widen (M i) (M (i + 1)) → M' (i + 1) = f i := fun i h => if_pos h
  have hneg : ∀ i, ¬ (i < n ∧ Widen (M i) (M (i + 1))) → M' (i + 1) = M (i + 1) := fun i h => if_neg h
  have hself : ∀ i, (∃ L, Widen (M i) L) → M' i = M i := by
    intro i ⟨L, hw⟩
    cases i with
    | zero => rfl
    | succ j => exact hneg j (fun h => noWW h.2 hw)
  refine ⟨M', fun i hi => ?_, rfl, ?_⟩
  · by_cases hw : Widen (M i) (M (i + 1))
    · rw [hpos i ⟨hi, hw⟩, hself i ⟨_, hw⟩]
      exact (hf i ⟨hi, hw⟩).1
    · have hR : R (M i) (M (i + 1)) := (hp i hi).resolve_right hw
      rw [hneg i (fun h => hw h.2)]
      cases i with
      | zero => exact hR
      | succ j =>
        by_cases hc : j < n ∧ Widen (M j) (M (j + 1))
        · rw [hpos j hc]; exact (hf j hc).2
        · rw [hneg j hc]; exact hR
  · cases n with
    | zero => rfl
    | succ m =>
      apply hneg m
      rintro ⟨_, _, _, _, _, _, h2, _, _⟩
      rw [hN] at h2; cases h2

/-- For c ≥ 0 and d ≥ 1: an `RPathX c d M n` with `NN (M 0)` and `M n` on a `T` kernel can be
replaced by an `RPath c d M' n` with the same endpoints. -/
theorem rpath_of_rpathX {c d : ℝ} (hc : 0 ≤ c) (hd : 1 ≤ d) {M : ℕ → RLine} {n : ℕ}
    (hp : RPathX c d M n) (h0 : NN (M 0)) {bl : List ℝ} {a' : ℝ} (hN : M n = (bl, .T a')) :
    ∃ M', RPath c d M' n ∧ M' 0 = M 0 ∧ M' n = M n :=
  path_unwiden (fun h hL => nn_step hc (by linarith) h hL)
    (fun ha0 ha he h => widen_dec hc hd ha0 ha he h) hp h0 hN

/-- `HY.Incl` is a `Widen` step between the encodings. -/
theorem widen_of_incl {L L' : HY.Line} (h : HY.Incl L L') : Widen (enc L) (enc L') := by
  cases h with
  | mk bl a => exact ⟨_, a, a, a, rfl, rfl, le_rfl, le_rfl⟩

/-- `HY.SpeedLog` is a `Loose` step between the encodings. -/
theorem loose_of_speedLog {L L' : HY.Line} (h : HY.SpeedLog L L') : Loose (enc L) (enc L') := by
  cases h with
  | merge u rest a e x ℓ ha he hex hx hx1 hb hℓ =>
    exact Loose.speedM u.o (rest.map HY.Blk.o) a e x (max u.o (x + e)) ℓ (a - x) e hx hex
      le_rfl hℓ le_rfl le_rfl
  | new bl q a e x ℓ hq ha he hex hx hx1 hb hℓ =>
    exact Loose.speedN (bl.map HY.Blk.o) a e x (max (HY.pin bl) (x + e)) ℓ (a - x) e hx hex
      (max_le_max (pin_le bl) le_rfl) hℓ le_rfl le_rfl

section oneLevel

variable {c d g : ℝ}

/-- Under `Facts c d g`, a `Loose` step from a line with nonnegative entries does not lower the
one-level potential `Phi c g`. -/
theorem phi_loose (F : Facts c d g) {L L' : RLine} (h : Loose L L') (hL : NN L) :
    Phi c g L ≤ Phi c g L' := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  have hL' := nn_loose h hL
  obtain ⟨hb, hk⟩ := hL
  cases h with
  | speedM b rest a e x b' L a₂ e₂ hx hex h' hL ha he =>
    simp only [Phi, pot, up]
    apply up_mono F
    have hb0 : 0 ≤ b := hb b (by simp)
    exact speed_ineq F hb0 (le_trans (le_max_left _ _) h')
      (le_trans (by linarith) (le_trans (le_max_right _ _) h'))
  | speedN bl a e x g₁ g₂ a₂ e₂ hx hex h₁ h₂ ha he =>
    cases bl with
    | nil =>
      simp only [Phi]
      exact Phi_nonneg F hL'
    | cons b rest =>
      simp only [Phi, pot, up]
      apply up_mono F
      have hb0 : 0 ≤ b := hb b (by simp)
      have h₁' : max b (x + e) ≤ g₁ := by simpa [pin] using h₁
      have hS : psS c b a e ≤ psT c g g₁ (c * max g₁ (psS c g₂ a₂ e₂)) :=
        speed_ineq F hb0 (le_trans (le_max_left _ _) h₁')
          (le_trans (by linarith) (le_trans (le_max_right _ _) h₁'))
      have hg₁0 : 0 ≤ g₁ := le_trans (le_trans hb0 (le_max_left _ _)) h₁'
      have hbY : b ≤ psT c g g₁ (c * max g₁ (psS c g₂ a₂ e₂)) :=
        le_trans (le_trans (le_max_left _ _) h₁') (psT_ge F hg₁0)
      exact le_trans hS (push_ineq F hb0 hbY)

/-- Under `Facts c d g` with d ≥ 1: along an `RPathW c d M n` from `M 0 = ([], T a₀)`, a₀ ≥ 0, to
`M n = ([], T a')`, a₀ ≤ a'. -/
theorem qf_ge_W (F : Facts c d g) (hd : 1 ≤ d) {M : ℕ → RLine} {n : ℕ} (hp : RPathW c d M n)
    {a₀ a' : ℝ} (ha₀ : 0 ≤ a₀) (h0 : M 0 = ([], .T a₀)) (hN : M n = ([], .T a')) : a₀ ≤ a' := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  have hnnR : ∀ {L L' : RLine}, (RStep c d L L' ∨ Loose L L') → NN L → NN L' := by
    intro L L' h hL
    rcases h with h | h
    · exact nn_step hc0 F.d0 h hL
    · exact nn_loose h hL
  have hM0 : NN (M 0) := by rw [h0]; exact ⟨by simp, by simpa [KNN] using ha₀⟩
  obtain ⟨M', hp', h0', hN'⟩ := path_unwiden (R := fun L L' => RStep c d L L' ∨ Loose L L')
    hnnR (fun ha0 ha he h => widen_dec_W hc0 hd ha0 ha he h) hp hM0 hN
  rw [h0] at h0'
  rw [hN] at hN'
  have hnn : ∀ i ≤ n, NN (M' i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0']; exact ⟨by simp, by simpa [KNN] using ha₀⟩
    | succ j ih => intro hj; exact hnnR (hp' j (by omega)) (ih (by omega))
  have hmono : ∀ i ≤ n, Phi c g (M' 0) ≤ Phi c g (M' i) := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ j ih =>
      intro hj
      refine le_trans (ih (by omega)) ?_
      rcases hp' j (by omega) with h | h
      · exact phi_step F h (hnn j (by omega))
      · exact phi_loose F h (hnn j (by omega))
  have := hmono n le_rfl
  rw [h0', hN'] at this
  simpa [Phi] using this

end oneLevel

/-- For real d ≥ 1, c ≥ 1 and c² ≥ 1 + 1/d: along every path `M 0, …, M n` of `HY.Step c d`,
`HY.Incl` and `HY.SpeedLog` steps from `([], T a₀)`, a₀ ≥ 0, to `([], T a')`, a₀ ≤ a'. In
particular no such path has a' < a₀. -/
theorem no_drop_W {c d : ℝ} (hd : 1 ≤ d) (hc : 1 ≤ c) (hcd : 1 + 1 / d ≤ c ^ 2) (M : ℕ → HY.Line)
    (n : ℕ) (hp : ∀ i < n, HY.Step c d (M i) (M (i + 1)) ∨ HY.Incl (M i) (M (i + 1)) ∨
      HY.SpeedLog (M i) (M (i + 1)))
    {a₀ a' : ℝ} (ha₀ : 0 ≤ a₀) (h0 : M 0 = ([], .T a₀)) (hN : M n = ([], .T a')) : a₀ ≤ a' := by
  have F := facts_of (by linarith) hc hcd
  refine qf_ge_W F hd (M := fun i => enc (M i)) (fun i hi => ?_) ha₀
    (by show enc (M 0) = _; rw [h0]; rfl) (by show enc (M n) = _; rw [hN]; rfl)
  rcases hp i hi with h | h | h
  · exact Or.inl (Or.inl (sim (by linarith) h))
  · exact Or.inr (widen_of_incl h)
  · exact Or.inl (Or.inr (loose_of_speedLog h))

/-- If ℓ o e ≥ 0 whenever o ≥ 1 and e ≥ 0 (for example under `HY.LogOK ℓ`), every `HY.StepO ℓ c d` step
is an `HY.Step c d` step or an `HY.SpeedLog` step. -/
theorem stepO_cases {ℓ : ℝ → ℝ → ℝ} (hℓ : ∀ o e : ℝ, 1 ≤ o → 0 ≤ e → 0 ≤ ℓ o e) {c d : ℝ}
    {L L' : HY.Line} (h : HY.StepO ℓ c d L L') : HY.Step c d L L' ∨ HY.SpeedLog L L' := by
  cases h with
  | convMerge u rest a s hs hsa hb => exact Or.inl (HY.Step.convMerge u rest a s hs hsa hb)
  | convNew bl q a s hq hs hsa hb => exact Or.inl (HY.Step.convNew bl q a s hq hs hsa hb)
  | speedMerge u rest a e x ha he hex hx hx1 hb =>
    exact Or.inr (HY.SpeedLog.merge u rest a e x _ ha he hex hx hx1 hb (hℓ _ _ hb he))
  | speedNew bl q a e x hq ha he hex hx hx1 hb =>
    exact Or.inr (HY.SpeedLog.new bl q a e x _ hq ha he hex hx hx1 hb (hℓ _ _ hb he))
  | slow u rest k h1 h2 h3 h4 => exact Or.inl (HY.Step.slow u rest k h1 h2 h3 h4)

/-- For real d ≥ 1, c ≥ 1 and c² ≥ 1 + 1/d, and every log n output ℓ with ℓ o e ≥ 0 whenever o ≥ 1 and
e ≥ 0 (in particular every ℓ with `HY.LogOK ℓ`): there is no strict normal-form proof `HY.NFO ℓ c d M n`. -/
theorem no_nfO {ℓ : ℝ → ℝ → ℝ} (hℓ : ∀ o e : ℝ, 1 ≤ o → 0 ≤ e → 0 ≤ ℓ o e) {c d : ℝ} (hd : 1 ≤ d)
    (hc : 1 ≤ c) (hcd : 1 + 1 / d ≤ c ^ 2) (M : ℕ → HY.Line) (n : ℕ) : ¬ HY.NFO ℓ c d M n := by
  rintro ⟨_, hp, ⟨a₀, h0⟩, ⟨a', hN⟩, _, h1, hlt, _⟩
  have hT0 : (M 0).2.time = a₀ := by rw [h0]; rfl
  have hTn : (M n).2.time = a' := by rw [hN]; rfl
  have := no_drop_W hd hc hcd M n
    (fun i hi => (stepO_cases hℓ (hp i hi)).elim Or.inl (fun h => Or.inr (Or.inr h)))
    (by linarith) h0 hN
  linarith

/-- For c ≥ 0: if an `RPathW c d` path of length n ≥ 1 ends at a line `(P, T a')`, its last step is a
relaxed slowdown (no other `RStep`, `Loose` or `Widen` step gives a `T` kernel), so c · pin P ≤ a'. -/
theorem rpathW_last_T {c d : ℝ} (hc : 0 ≤ c) {M : ℕ → RLine} {n : ℕ} (hp : RPathW c d M n)
    (hn : 1 ≤ n) {P : List ℝ} {a' : ℝ} (hN : M n = (P, .T a')) : c * pin P ≤ a' := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases hp m (by omega) with (h | h) | h <;> rw [hN] at h <;> generalize M m = L at h
  · cases h with
    | slow b rest k a' hh =>
      exact le_trans (mul_le_mul_of_nonneg_left (le_max_of_le_left (le_max_left _ _)) hc) hh
  · cases h
  · obtain ⟨_, _, _, _, _, h2, _, _⟩ := h
    cases h2

end HL

namespace HLM

open HL

/-- If `Hyp c₀ d θ₀ lv`, every θ > 1, 1 < c₀, c₀ ≤ c and d ≥ 1: (1) there is no `RPathX c d M n`
with n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` with a' ≤ a₀; (2) every path of `HY.Step c d`
and `HY.Incl` steps of length n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` has a₀ < a'. -/
theorem ceilingX_of {c₀ d θ₀ : ℝ} {lv : List (ℝ × ℝ)} (H : Hyp c₀ d θ₀ lv)
    (ht : ∀ p ∈ (0, θ₀) :: lv, 1 < p.2) (hc1 : 1 < c₀) (hd : 1 ≤ d) {c : ℝ} (hc : c₀ ≤ c) :
    (¬ ∃ (M : ℕ → RLine) (n : ℕ) (a₀ a' : ℝ), RPathX c d M n ∧ 1 ≤ n ∧ 0 < a₀ ∧
      M 0 = ([], .T a₀) ∧ M n = ([], .T a') ∧ a' ≤ a₀) ∧
    (∀ (M : ℕ → HY.Line) (n : ℕ), 1 ≤ n →
      (∀ i < n, HY.Step c d (M i) (M (i + 1)) ∨ HY.Incl (M i) (M (i + 1))) → ∀ a₀ a' : ℝ, 0 < a₀ →
      M 0 = ([], .T a₀) → M n = ([], .T a') → a₀ < a') := by
  have hc0 : 0 ≤ c := by linarith
  have gt : ∀ (M : ℕ → RLine) (n : ℕ) (a₀ a' : ℝ), RPathX c d M n → 1 ≤ n → 0 < a₀ →
      M 0 = ([], .T a₀) → M n = ([], .T a') → a₀ < a' := by
    intro M n a₀ a' hp hn ha₀ h0 hN
    obtain ⟨M', hp', h0', hN'⟩ :=
      rpath_of_rpathX hc0 hd hp (by rw [h0]; exact ⟨by simp, by simpa [KNN] using ha₀.le⟩) hN
    exact rgt_of H ht hc1 hc hp' hn ha₀ (h0'.trans h0) (hN'.trans hN)
  refine ⟨?_, fun M n hn hp a₀ a' ha₀ h0 hN => ?_⟩
  · rintro ⟨M, n, a₀, a', hp, hn, ha₀, h0, hN, hle⟩
    have := gt M n a₀ a' hp hn ha₀ h0 hN
    linarith
  · refine gt (fun i => enc (M i)) n a₀ a' (fun i hi => ?_) hn ha₀
      (by show enc (M 0) = _; rw [h0]; rfl) (by show enc (M n) = _; rw [hN]; rfl)
    rcases hp i hi with h | h
    · exact Or.inl (sim hc0 h)
    · exact Or.inr (widen_of_incl h)

/-- For every real c ≥ 6547/5000 = 1.3094, with d = 1: (1) there is no `RPathX c 1 M n` with n ≥ 1
from `([], T a₀)`, a₀ > 0, to `([], T a')` with a' ≤ a₀; (2) every path of `HY.Step c 1` and
`HY.Incl` steps of length n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` has a₀ < a'. -/
theorem ceilingX_d1 {c : ℝ} (hc : (6547 / 5000 : ℝ) ≤ c) :
    (¬ ∃ (M : ℕ → RLine) (n : ℕ) (a₀ a' : ℝ), RPathX c 1 M n ∧ 1 ≤ n ∧ 0 < a₀ ∧
      M 0 = ([], .T a₀) ∧ M n = ([], .T a') ∧ a' ≤ a₀) ∧
    (∀ (M : ℕ → HY.Line) (n : ℕ), 1 ≤ n →
      (∀ i < n, HY.Step c 1 (M i) (M (i + 1)) ∨ HY.Incl (M i) (M (i + 1))) → ∀ a₀ a' : ℝ, 0 < a₀ →
      M 0 = ([], .T a₀) → M n = ([], .T a') → a₀ < a') := by
  have H := hypD1
  have hd : (((1 : ℚ) : ℚ) : ℝ) = 1 := by norm_num
  rw [hd] at H
  exact ceilingX_of H thD1_gt (by norm_num) le_rfl (by push_cast; linarith)

/-- For every real c ≥ 149/125 = 1.192, with d = 2: (1) there is no `RPathX c 2 M n` with n ≥ 1
from `([], T a₀)`, a₀ > 0, to `([], T a')` with a' ≤ a₀; (2) every path of `HY.Step c 2` and
`HY.Incl` steps of length n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` has a₀ < a'. -/
theorem ceilingX_d2 {c : ℝ} (hc : (149 / 125 : ℝ) ≤ c) :
    (¬ ∃ (M : ℕ → RLine) (n : ℕ) (a₀ a' : ℝ), RPathX c 2 M n ∧ 1 ≤ n ∧ 0 < a₀ ∧
      M 0 = ([], .T a₀) ∧ M n = ([], .T a') ∧ a' ≤ a₀) ∧
    (∀ (M : ℕ → HY.Line) (n : ℕ), 1 ≤ n →
      (∀ i < n, HY.Step c 2 (M i) (M (i + 1)) ∨ HY.Incl (M i) (M (i + 1))) → ∀ a₀ a' : ℝ, 0 < a₀ →
      M 0 = ([], .T a₀) → M n = ([], .T a') → a₀ < a') := by
  have H := hypD2
  have hd : (((2 : ℚ) : ℚ) : ℝ) = 2 := by norm_num
  rw [hd] at H
  exact ceilingX_of H thD2_gt (by norm_num) (by norm_num) (by push_cast; linarith)

/-- For every real c ≥ 712/625 = 1.1392, with d = 3: (1) there is no `RPathX c 3 M n` with n ≥ 1
from `([], T a₀)`, a₀ > 0, to `([], T a')` with a' ≤ a₀; (2) every path of `HY.Step c 3` and
`HY.Incl` steps of length n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')` has a₀ < a'. -/
theorem ceilingX_d3 {c : ℝ} (hc : (712 / 625 : ℝ) ≤ c) :
    (¬ ∃ (M : ℕ → RLine) (n : ℕ) (a₀ a' : ℝ), RPathX c 3 M n ∧ 1 ≤ n ∧ 0 < a₀ ∧
      M 0 = ([], .T a₀) ∧ M n = ([], .T a') ∧ a' ≤ a₀) ∧
    (∀ (M : ℕ → HY.Line) (n : ℕ), 1 ≤ n →
      (∀ i < n, HY.Step c 3 (M i) (M (i + 1)) ∨ HY.Incl (M i) (M (i + 1))) → ∀ a₀ a' : ℝ, 0 < a₀ →
      M 0 = ([], .T a₀) → M n = ([], .T a') → a₀ < a') := by
  have H := hypD3
  have hd : (((3 : ℚ) : ℚ) : ℝ) = 3 := by norm_num
  rw [hd] at H
  exact ceilingX_of H thD3_gt (by norm_num) (by norm_num) (by push_cast; linarith)

end HLM
end PastaMath.OneTapeThreshold
