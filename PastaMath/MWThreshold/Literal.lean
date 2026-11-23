-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Data.Rat.Cast.Order
import PastaMath.MWThreshold.Limit

/-!
# The Mudigonda–Williams BPTS calculus in its own line format

The calculus of A. S. Mudigonda and R. Williams (ITCS 2021; arXiv 2012.00330, Definition 2.14
rules 2–5, with Theorem 2.10, Corollaries 2.8 and 2.11 and Lemma 5.1) for ∃·BPTIME[n] versus BPTS,
with its exact rule outputs.

A line is `(Q₁ n^{g₁})^{o₁} ⋯ K[n^a]`, blocks innermost first, `q = true` for ∃, kernel BPTS
(`true`) or TS (`false`); the superscript in front of the first block is 1 (input length n).
* `rspeed0` (rule 3, Thm 2.10): BPTS[n^a] ⊆ (∃ n^0)^1 (∀ n^x)^{max(x,1)} (∃ x log n)^1 TS[n^{a−x}],
  0 < x < a;
* `rspeed` (rule 4, Cor. 2.11, the new n^0 block absorbed into the innermost block):
  ⋯(Q n^g)^o BPTS[n^a] ⊆ ⋯(Q n^g)^o (¬Q n^x)^{max(o,x)} (Q x log n)^o TS[n^{a−x}], 0 < x < a;
* `dspeed` (rule 2, Cor. 2.8): ⋯(Q n^g)^o TS[n^a] ⊆ ⋯(Q n^{max(g,x)})^{max(o,x)} (¬Q x log n)^o
  TS[n^{a−x}], 0 < x < a;
* `slow` (rule 5, Lemma 5.1, α = 1): ⋯^{o'} (Q n^g)^o K[n^a] ⊆ ⋯^{o'} BPTS[n^{c·max(a, o, g, o')}].
A refutation (`Refutes`; Definition 2.14 and Lemma 5.2) is strict: BPTS[n^{a₀}] ⊆ … ⊆ BPTS[n^{a'}],
a' < a₀, with at least one step.

`lit_m` maps every literal step to a step of the relaxed calculus `MW.MStep`, so
`MW.no_mrefutation` applies (`no_lit_refutation`). `StepU` adds the unmerged orientation of rule 4
and `StepW` adds weakening of an existing line; both are covered as well (`no_litU_refutation`,
`no_litW_refutation`). `checkQ_sound` turns a rational tag list accepted by the executable checker
`checkQ` into a refutation.
-/

namespace PastaMath.MWThreshold
namespace MWL

structure Blk where
  q : Bool
  g : ℝ
  o : ℝ

abbrev Line := List Blk × Bool × ℝ

def pin : List Blk → ℝ
  | [] => 1
  | u :: _ => u.o

inductive Step (c : ℝ) : Line → Line → Prop
  | rspeed0 (a x : ℝ) (hx : 0 < x) (hxa : x < a) :
      Step c ([], true, a) ([⟨true, 0, 1⟩, ⟨false, x, max x 1⟩, ⟨true, 0, 1⟩], false, a - x)
  | rspeed (u : Blk) (rest : List Blk) (a x : ℝ) (hx : 0 < x) (hxa : x < a) :
      Step c (u :: rest, true, a) (⟨u.q, 0, u.o⟩ :: ⟨!u.q, x, max u.o x⟩ :: u :: rest, false, a - x)
  | dspeed (u : Blk) (rest : List Blk) (a x : ℝ) (hx : 0 < x) (hxa : x < a) :
      Step c (u :: rest, false, a) (⟨!u.q, 0, u.o⟩ :: ⟨u.q, max u.g x, max u.o x⟩ :: rest, false, a - x)
  | slow (u : Blk) (rest : List Blk) (k : Bool) (a : ℝ) :
      Step c (u :: rest, k, a) (rest, true, c * max (max a u.o) (max u.g (pin rest)))

def Path (c : ℝ) (M : ℕ → Line) (n : ℕ) : Prop := ∀ i < n, Step c (M i) (M (i + 1))

def Refutes (c : ℝ) (n : ℕ) (M : ℕ → Line) : Prop :=
  1 ≤ n ∧ Path c M n ∧ ∃ a₀ a', 0 < a₀ ∧ M 0 = ([], true, a₀) ∧ M n = ([], true, a') ∧ a' < a₀

/-- Invariant used by the encoding: every guess exponent is ≥ 0 and ≤ its output superscript, every
output superscript is ≥ 0, and the kernel is ≥ 0. -/
def Inv (L : Line) : Prop := (∀ u ∈ L.1, 0 ≤ u.g ∧ u.g ≤ u.o ∧ 0 ≤ u.o) ∧ 0 ≤ L.2.2

def enc (L : Line) : MW.MLine := (L.1.map Blk.o, L.2.1, L.2.2)

theorem pin_enc (bl : List Blk) (h : ∀ u ∈ bl, 0 ≤ u.o) : MW.pin (bl.map Blk.o) ≤ pin bl := by
  cases bl with
  | nil => simp [MW.pin, pin]
  | cons u _ => simp [MW.pin, pin]

theorem lit_m {c : ℝ} (hc : 0 ≤ c) {L L' : Line} (h : Step c L L') (hI : Inv L) :
    MW.MStep c (enc L) (enc L') ∧ Inv L' := by
  obtain ⟨hb, ha⟩ := hI
  cases h with
  | rspeed0 a x hx hxa =>
    refine ⟨?_, ?_, ?_⟩
    · exact MW.MStep.rspeed0 true a x 1 (max x 1) 1 (a - x) hx.le hxa.le (by norm_num)
        (le_max_left _ _) (le_trans zero_le_one (le_max_right _ _)) (by norm_num) le_rfl
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · norm_num
      · exact ⟨hx.le, le_max_left _ _, le_trans zero_le_one (le_max_right _ _)⟩
      · norm_num
    · show 0 ≤ a - x; linarith
  | rspeed u rest a x hx hxa =>
    obtain ⟨hg0, hgo, ho0⟩ := hb u (by simp)
    refine ⟨?_, ?_, ?_⟩
    · exact MW.MStep.rspeed u.o (rest.map Blk.o) true a x (max u.o x) u.o (a - x) hx.le hxa.le
        le_rfl le_rfl le_rfl
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | rfl | rfl | hv
      · exact ⟨le_rfl, ho0, ho0⟩
      · exact ⟨hx.le, le_max_right _ _, le_trans ho0 (le_max_left _ _)⟩
      · exact ⟨hg0, hgo, ho0⟩
      · exact hb v (by simp [hv])
    · show 0 ≤ a - x; linarith
  | dspeed u rest a x hx hxa =>
    obtain ⟨hg0, hgo, ho0⟩ := hb u (by simp)
    refine ⟨?_, ?_, ?_⟩
    · exact MW.MStep.dspeed u.o (rest.map Blk.o) a x (max u.o x) u.o (a - x) hx.le hxa.le
        le_rfl le_rfl le_rfl
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | rfl | hv
      · exact ⟨le_rfl, ho0, ho0⟩
      · exact ⟨le_trans hg0 (le_max_left _ _), max_le_max hgo le_rfl,
          le_trans ho0 (le_max_left _ _)⟩
      · exact hb v (by simp [hv])
    · show 0 ≤ a - x; linarith
  | slow u rest k a =>
    obtain ⟨hg0, hgo, ho0⟩ := hb u (by simp)
    have hrest : ∀ v ∈ rest, 0 ≤ v.o := fun v hv => (hb v (by simp [hv])).2.2
    refine ⟨?_, fun v hv => hb v (by simp [hv]), ?_⟩
    · apply MW.MStep.slow u.o (rest.map Blk.o) k a
      apply mul_le_mul_of_nonneg_left _ hc
      have hp := pin_enc rest hrest
      apply max_le (max_le ?_ ?_) ?_
      · exact le_trans hp (le_trans (le_max_right _ _) (le_max_right _ _))
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · show 0 ≤ c * max (max a u.o) (max u.g (pin rest))
      exact mul_nonneg hc (le_trans ha (le_trans (le_max_left _ _) (le_max_left _ _)))

/-- No literal refutation for c ≥ φ (via the relaxed calculus). -/
theorem no_lit_refutation {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) (n : ℕ) (M : ℕ → Line) :
    ¬ Refutes c n M := by
  rintro ⟨hn, hp, a₀, a', ha₀, h0, hN, hlt⟩
  have hI : ∀ i ≤ n, Inv (M i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ⟨by simp, ha₀.le⟩
    | succ j ih => intro hj; exact (lit_m hc0.le (hp j (by omega)) (ih (by omega))).2
  apply MW.no_mrefutation hc0 hphi n (fun i => enc (M i))
  refine ⟨hn, fun i hi => (lit_m hc0.le (hp i hi) (hI i hi.le)).1, a₀, a', ha₀, ?_, ?_, hlt.le⟩
  · show enc (M 0) = _; rw [h0]; rfl
  · show enc (M n) = _; rw [hN]; rfl

/-! ### Rational checker -/

structure BlkQ where
  q : Bool
  g : ℚ
  o : ℚ
  deriving DecidableEq

abbrev LineQ := List BlkQ × Bool × ℚ

def pinQ : List BlkQ → ℚ
  | [] => 1
  | u :: _ => u.o

/-- Tags: `r x` = randomized speedup (rule 3 on the empty line, rule 4 otherwise), `d x` = rule 2,
`s` = slowdown. -/
inductive Tag
  | r (x : ℚ)
  | d (x : ℚ)
  | s

def stepQ (c : ℚ) : Tag → LineQ → Option LineQ
  | .r x, ([], true, a) =>
      if decide (0 < x) && decide (x < a) then
        some ([⟨true, 0, 1⟩, ⟨false, x, max x 1⟩, ⟨true, 0, 1⟩], false, a - x) else none
  | .r x, (u :: rest, true, a) =>
      if decide (0 < x) && decide (x < a) then
        some (⟨u.q, 0, u.o⟩ :: ⟨!u.q, x, max u.o x⟩ :: u :: rest, false, a - x) else none
  | .d x, (u :: rest, false, a) =>
      if decide (0 < x) && decide (x < a) then
        some (⟨!u.q, 0, u.o⟩ :: ⟨u.q, max u.g x, max u.o x⟩ :: rest, false, a - x) else none
  | .s, (u :: rest, _, a) => some (rest, true, c * max (max a u.o) (max u.g (pinQ rest)))
  | _, _ => none

/-- Run the tags from BPTS[n^{a0}] and accept iff the last line is BPTS[n^{a'}] with a' < a0. -/
def runQ (c : ℚ) : LineQ → List Tag → Option LineQ
  | L, [] => some L
  | L, t :: ts =>
      match stepQ c t L with
      | none => none
      | some M => runQ c M ts

def checkQ (c a0 : ℚ) (ts : List Tag) : Bool :=
  decide (0 < a0) && decide (1 ≤ ts.length) &&
    match runQ c ([], true, a0) ts with
    | some ([], true, a') => decide (a' < a0)
    | _ => false

def castB (u : BlkQ) : Blk := ⟨u.q, (u.g : ℝ), (u.o : ℝ)⟩

def castL (L : LineQ) : Line := (L.1.map castB, L.2.1, (L.2.2 : ℝ))

theorem pin_cast (bl : List BlkQ) : pin (bl.map castB) = (pinQ bl : ℝ) := by
  cases bl <;> simp [pin, pinQ, castB]

theorem stepQ_sound {c : ℚ} {t : Tag} {L M : LineQ} (h : stepQ c t L = some M) :
    Step (c : ℝ) (castL L) (castL M) := by
  obtain ⟨bl, k, a⟩ := L
  cases t with
  | r x =>
    cases bl with
    | nil =>
      cases k
      · simp [stepQ] at h
      · simp only [stepQ] at h
        split_ifs at h with hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        cases h
        have := Step.rspeed0 (c := (c : ℝ)) (a : ℝ) (x : ℝ) (by exact_mod_cast hc.1)
          (by exact_mod_cast hc.2)
        simpa [castL, castB] using this
    | cons u rest =>
      cases k
      · simp [stepQ] at h
      · simp only [stepQ] at h
        split_ifs at h with hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        cases h
        have := Step.rspeed (c := (c : ℝ)) (castB u) (rest.map castB) (a : ℝ) (x : ℝ)
          (by exact_mod_cast hc.1) (by exact_mod_cast hc.2)
        simpa [castL, castB] using this
  | d x =>
    cases bl with
    | nil => cases k <;> simp [stepQ] at h
    | cons u rest =>
      cases k
      · simp only [stepQ] at h
        split_ifs at h with hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        cases h
        have := Step.dspeed (c := (c : ℝ)) (castB u) (rest.map castB) (a : ℝ) (x : ℝ)
          (by exact_mod_cast hc.1) (by exact_mod_cast hc.2)
        simpa [castL, castB] using this
      · simp [stepQ] at h
  | s =>
    cases bl with
    | nil => simp [stepQ] at h
    | cons u rest =>
      simp only [stepQ, Option.some.injEq] at h
      subst h
      have := Step.slow (c := (c : ℝ)) (castB u) (rest.map castB) k (a : ℝ)
      simpa [castL, castB, pin_cast] using this

theorem runQ_sound {c : ℚ} : ∀ (ts : List Tag) (L Lf : LineQ), runQ c L ts = some Lf →
    ∃ M : ℕ → Line, M 0 = castL L ∧ M ts.length = castL Lf ∧ Path (c : ℝ) M ts.length
  | [], L, Lf, h => by
      simp only [runQ, Option.some.injEq] at h
      subst h
      exact ⟨fun _ => castL L, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | t :: ts, L, Lf, h => by
      simp only [runQ] at h
      split at h
      · simp at h
      · rename_i M1 hM
        obtain ⟨M, h0, hN, hp⟩ := runQ_sound ts M1 Lf h
        refine ⟨fun i => if i = 0 then castL L else M (i - 1), by simp, ?_, ?_⟩
        · simp [hN]
        · intro i hi
          cases i with
          | zero => simpa [h0] using stepQ_sound hM
          | succ j =>
            have := hp j (by simp at hi; omega)
            simpa using this

theorem checkQ_sound {c a0 : ℚ} {ts : List Tag} (h : checkQ c a0 ts = true) :
    ∃ n M, Refutes (c : ℝ) n M := by
  unfold checkQ at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ha0, hn⟩, hr⟩ := h
  cases hrun : runQ c ([], true, a0) ts with
  | none => simp [hrun] at hr
  | some Lf =>
    rw [hrun] at hr
    obtain ⟨bl, k, a'⟩ := Lf
    cases bl with
    | cons _ _ => simp at hr
    | nil =>
      cases k
      · simp at hr
      · simp only [decide_eq_true_eq] at hr
        obtain ⟨M, h0, hN, hp⟩ := runQ_sound ts _ _ hrun
        refine ⟨ts.length, M, hn, hp, (a0 : ℝ), (a' : ℝ), by exact_mod_cast ha0, ?_, ?_,
          by exact_mod_cast hr⟩
        · rw [h0]; rfl
        · rw [hN]; rfl


/-! ### The unmerged randomized speedup -/

/-- The literal calculus with the unmerged orientation of rule 4 added:
⋯(Q n^g)^o BPTS[n^a] ⊆ ⋯(Q n^g)^o (¬Q n^0)^o (Q n^x)^{max(o,x)} (¬Q x log n)^o TS[n^{a−x}]. -/
inductive StepU (c : ℝ) : Line → Line → Prop
  | lit {L L' : Line} : Step c L L' → StepU c L L'
  | rspeedU (u : Blk) (rest : List Blk) (a x : ℝ) (hx : 0 < x) (hxa : x < a) :
      StepU c (u :: rest, true, a)
        (⟨!u.q, 0, u.o⟩ :: ⟨u.q, x, max u.o x⟩ :: ⟨!u.q, 0, u.o⟩ :: u :: rest, false, a - x)

def PathU (c : ℝ) (M : ℕ → Line) (n : ℕ) : Prop := ∀ i < n, StepU c (M i) (M (i + 1))

def RefutesU (c : ℝ) (n : ℕ) (M : ℕ → Line) : Prop :=
  1 ≤ n ∧ PathU c M n ∧ ∃ a₀ a', 0 < a₀ ∧ M 0 = ([], true, a₀) ∧ M n = ([], true, a') ∧ a' ≤ a₀

theorem lit_u {c : ℝ} (hc : 0 ≤ c) {L L' : Line} (h : StepU c L L') (hI : Inv L) :
    MW.UStep c (enc L) (enc L') ∧ Inv L' := by
  cases h with
  | lit h => exact ⟨MW.UStep.base (lit_m hc h hI).1, (lit_m hc h hI).2⟩
  | rspeedU u rest a x hx hxa =>
    obtain ⟨hb, ha⟩ := hI
    obtain ⟨hg0, hgo, ho0⟩ := hb u (by simp)
    refine ⟨?_, ?_, ?_⟩
    · exact MW.UStep.rspeedU u.o (rest.map Blk.o) true a x u.o (max u.o x) u.o (a - x) hx.le hxa.le
        ho0 le_rfl le_rfl le_rfl
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | rfl | rfl | rfl | hv
      · exact ⟨le_rfl, ho0, ho0⟩
      · exact ⟨hx.le, le_max_right _ _, le_trans ho0 (le_max_left _ _)⟩
      · exact ⟨le_rfl, ho0, ho0⟩
      · exact ⟨hg0, hgo, ho0⟩
      · exact hb v (by simp [hv])
    · show 0 ≤ a - x; linarith

/-- No refutation (strict or non-strict) for c ≥ φ in the literal calculus with both orientations of
the randomized speedup. -/
theorem no_litU_refutation {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) (n : ℕ) (M : ℕ → Line) :
    ¬ RefutesU c n M := by
  rintro ⟨hn, hp, a₀, a', ha₀, h0, hN, hle⟩
  have hI : ∀ i ≤ n, Inv (M i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ⟨by simp, ha₀.le⟩
    | succ j ih => intro hj; exact (lit_u hc0.le (hp j (by omega)) (ih (by omega))).2
  apply MW.no_urefutation hc0 hphi n (fun i => enc (M i))
  refine ⟨hn, fun i hi => (lit_u hc0.le (hp i hi) (hI i hi.le)).1, a₀, a', ha₀, ?_, ?_, hle⟩
  · show enc (M 0) = _; rw [h0]; rfl
  · show enc (M n) = _; rw [hN]; rfl


/-! ### Weakening -/

/-- Weakening of a literal line: the same quantifiers, every guess exponent, output superscript and
the kernel exponent raised (each guess exponent staying at most its superscript), and the kernel
kept or replaced by BPTS (TS ⊆ BPTS). -/
def LitWeaker (L L' : Line) : Prop :=
  List.Forall₂ (fun u v : Blk => u.q = v.q ∧ u.g ≤ v.g ∧ v.g ≤ v.o ∧ u.o ≤ v.o) L.1 L'.1 ∧
    (L.2.1 = L'.2.1 ∨ L'.2.1 = true) ∧ L.2.2 ≤ L'.2.2

/-- `StepU` plus weakening of an existing line. -/
inductive StepW (c : ℝ) : Line → Line → Prop
  | rule {L L' : Line} : StepU c L L' → StepW c L L'
  | weaken {L L' : Line} : LitWeaker L L' → StepW c L L'

def PathW (c : ℝ) (M : ℕ → Line) (n : ℕ) : Prop := ∀ i < n, StepW c (M i) (M (i + 1))

/-- A non-strict refutation with weakening, at least one step being a rule step. -/
def RefutesW (c : ℝ) (n : ℕ) (M : ℕ → Line) : Prop :=
  PathW c M n ∧ (∃ j < n, StepU c (M j) (M (j + 1))) ∧
    ∃ a₀ a', 0 < a₀ ∧ M 0 = ([], true, a₀) ∧ M n = ([], true, a') ∧ a' ≤ a₀

theorem forall₂_inv {l l' : List Blk}
    (h : List.Forall₂ (fun u v : Blk => u.q = v.q ∧ u.g ≤ v.g ∧ v.g ≤ v.o ∧ u.o ≤ v.o) l l')
    (hl : ∀ u ∈ l, 0 ≤ u.g ∧ u.g ≤ u.o ∧ 0 ≤ u.o) : ∀ v ∈ l', 0 ≤ v.g ∧ v.g ≤ v.o ∧ 0 ≤ v.o := by
  induction h with
  | nil => simp
  | @cons u v _ _ huv _ ih =>
    intro w hw
    simp only [List.mem_cons] at hw hl
    obtain ⟨hg0, _, ho0⟩ := hl u (Or.inl rfl)
    obtain ⟨_, hg, hgo, ho⟩ := huv
    rcases hw with rfl | hw
    · exact ⟨le_trans hg0 hg, hgo, le_trans ho0 ho⟩
    · exact ih (fun z hz => hl z (Or.inr hz)) w hw

theorem lit_w {c : ℝ} (hc : 0 ≤ c) {L L' : Line} (h : StepW c L L') (hI : Inv L) :
    MW.StepW c (enc L) (enc L') ∧ Inv L' := by
  cases h with
  | rule h => exact ⟨MW.StepW.rule (lit_u hc h hI).1, (lit_u hc h hI).2⟩
  | weaken h =>
    obtain ⟨hbs, hk, ha⟩ := h
    refine ⟨MW.StepW.weaken ⟨?_, hk, ha⟩, forall₂_inv hbs hI.1, le_trans hI.2 ha⟩
    show List.Forall₂ (· ≤ ·) (L.1.map Blk.o) (L'.1.map Blk.o)
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hbs.imp fun _ _ h => h.2.2.2

/-- No refutation (non-strict, at least one rule step) for c ≥ φ in the literal calculus with both
orientations of the randomized speedup and with weakening. -/
theorem no_litW_refutation {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) (n : ℕ) (M : ℕ → Line) :
    ¬ RefutesW c n M := by
  rintro ⟨hp, ⟨j, hj, hu⟩, a₀, a', ha₀, h0, hN, hle⟩
  have hI : ∀ i ≤ n, Inv (M i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ⟨by simp, ha₀.le⟩
    | succ j ih => intro hj; exact (lit_w hc0.le (hp j (by omega)) (ih (by omega))).2
  apply MW.no_wrefutation hc0 hphi n (fun i => enc (M i))
  refine ⟨fun i hi => (lit_w hc0.le (hp i hi) (hI i hi.le)).1,
    ⟨j, hj, (lit_u hc0.le hu (hI j hj.le)).1⟩, a₀, a', ha₀, ?_, ?_, hle⟩
  · show enc (M 0) = _; rw [h0]; rfl
  · show enc (M n) = _; rw [hN]; rfl

end MWL
end PastaMath.MWThreshold
