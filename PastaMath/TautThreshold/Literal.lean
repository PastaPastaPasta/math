-- SPDX-License-Identifier: Apache-2.0
import PastaMath.TautThreshold.Limit

/-!
# Williams's TAUT-vs-NTS calculus in its own line format

Formalisation of the calculus of W13 (R. Williams, "Alternation-trading proofs, linear
programming, and lower bounds", ACM TOCT 2013: §2 class syntax; §6 Lemmas 6.1, 6.2,
Definition 6.4, Theorem 6.6), mapped onto the reduced system `TL.TStep`.

A line `(bl, k, a)` is `(Q₁ n^{g₁})^{o₁} ⋯ (Q_m n^{g_m})^{o_m} K[n^a]` with the block list stored
innermost first: `bl = [B_m, …, B₁]`, `B.q = true` for ∃, `B.g` the guess exponent, `B.o` the
input constraint passed on (W13's b_{i+1}); `k = true` for an NTS kernel, `false` for coNTS.
The input constraint of an empty prefix is 1 (input length n).

* `WStepE` is the calculus with the exact values of Lemmas 6.1/6.2 (and the side conditions
  b ≥ 1, a ≥ 1, x ≥ 0 of Lemma 6.1), merging the new block into the innermost one when the types
  agree (W13 §2).
* `WStep` is its LP relaxation (every output only bounded below, no side conditions beyond
  x ≥ 0). `WStepE ⊆ WStep`.
* `WStepX` extends `WStep`: a speedup may open a new block next to an innermost block of the same
  type without merging, a matching kernel may be flipped in place, a quantifier-free kernel may be
  flipped, and two adjacent blocks of the same type anywhere in the prefix may be combined into
  one (W13 §2), or one block split into two. Lines need not alternate. `WStepXE` is the exact
  version. `WStep ⊆ WStepX` and `WStepXE ⊆ WStepX`.

That these rules cover W13's calculus is a modelling claim, not something Lean checks.

The encoding `enc` keeps one entry per maximal run of adjacent same-type blocks (the input
constraint of its innermost block), so combining and splitting are weakenings of the reduced line.

Main results: `sim`, `sim0` (every `WStepX` step is one or two `TStep`s, kernel clamped at 0);
`normal_form_gen` (W13 Theorem 6.6: a proof A ⊆ ¬A yields a normal-form proof); `no_nfX`; and
`no_proofX`: for c³ ≥ 4 no `WStepX` path of length ≥ 1 leads from any line A to a line B with
B ≤ ¬A (`LineLE`: same quantifiers and kernel type, every exponent of B at most that of ¬A).
`no_literal_proof`, `no_literal_proofE`, `no_proofXE` and `no_nf` are corollaries.
-/

namespace PastaMath.TautThreshold
namespace TW

open TL

structure Blk where
  q : Bool
  g : ℝ
  o : ℝ

abbrev WLine := List Blk × Bool × ℝ

def pin : List Blk → ℝ
  | [] => 1
  | u :: _ => u.o

/-- LP form of W13 §6. `speedNew`: Lemma 6.1 when no block or the innermost block has the other
type (opens `(∃ n^x)^{max(b,x)} (∀ log n)^b` for NTS, dual for coNTS); `speedMerge`: Lemma 6.1
when the innermost block has the new block's type (merged, W13 §2); `pop`: Lemma 6.2(1),(2);
`flip`: Lemma 6.2(3),(4). -/
inductive WStep (c : ℝ) : WLine → WLine → Prop
  | speedNew (bl : List Blk) (k : Bool) (a x g g₂ o₁ o₂ a₂ : ℝ)
      (hq : ∀ u rest, bl = u :: rest → u.q ≠ k) (hx : 0 ≤ x) (hg : x ≤ g) (hg₂ : 0 ≤ g₂)
      (h₁ : max (pin bl) x ≤ o₁) (h₂ : pin bl ≤ o₂) (h₃ : a - x ≤ a₂) :
      WStep c (bl, k, a) (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: bl, k, a₂)
  | speedMerge (u : Blk) (rest : List Blk) (k : Bool) (a x g g₂ o₁ o₂ a₂ : ℝ) (hq : u.q = k)
      (hx : 0 ≤ x) (hg : max u.g x ≤ g) (hg₂ : 0 ≤ g₂) (h₁ : max u.o x ≤ o₁) (h₂ : u.o ≤ o₂)
      (h₃ : a - x ≤ a₂) :
      WStep c (u :: rest, k, a) (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: rest, k, a₂)
  | pop (u : Blk) (rest : List Blk) (k : Bool) (a e : ℝ) (hq : u.q = k)
      (h : c * max (max u.g a) (max u.o (pin rest)) ≤ e) : WStep c (u :: rest, k, a) (rest, !k, e)
  | flip (u : Blk) (rest : List Blk) (k : Bool) (a e : ℝ) (hq : u.q ≠ k)
      (h : c * max a u.o ≤ e) : WStep c (u :: rest, k, a) (u :: rest, !k, e)

/-- The exact rules of W13 Lemmas 6.1 (with s = o(1)) and 6.2. -/
inductive WStepE (c : ℝ) : WLine → WLine → Prop
  | speedNew (bl : List Blk) (k : Bool) (a x : ℝ) (hq : ∀ u rest, bl = u :: rest → u.q ≠ k)
      (hb : 1 ≤ pin bl) (ha : 1 ≤ a) (hx : 0 ≤ x) :
      WStepE c (bl, k, a) (⟨!k, 0, pin bl⟩ :: ⟨k, x, max (pin bl) x⟩ :: bl, k, a - x)
  | speedMerge (u : Blk) (rest : List Blk) (k : Bool) (a x : ℝ) (hq : u.q = k) (hb : 1 ≤ u.o)
      (ha : 1 ≤ a) (hx : 0 ≤ x) :
      WStepE c (u :: rest, k, a) (⟨!k, 0, u.o⟩ :: ⟨k, max u.g x, max u.o x⟩ :: rest, k, a - x)
  | pop (u : Blk) (rest : List Blk) (k : Bool) (a : ℝ) (hq : u.q = k) :
      WStepE c (u :: rest, k, a) (rest, !k, c * max (max u.g a) (max u.o (pin rest)))
  | flip (u : Blk) (rest : List Blk) (k : Bool) (a : ℝ) (hq : u.q ≠ k) :
      WStepE c (u :: rest, k, a) (u :: rest, !k, c * max a u.o)

/-- The extended calculus (LP form). `speed`: Lemma 6.1 opening new blocks whatever the type of
the innermost block (so also a block of the same type as the innermost one, not merged);
`speedMerge`: Lemma 6.1 merged; `pop`: Lemma 6.2(1),(2), whatever the type of the next block;
`flip`: Lemma 6.2(3),(4) and the in-place flip of a matching kernel; `flipQ`: the
quantifier-free flip NTS[n^a] ⊆ coNTS[n^{c·max(a,1)}] and its dual; `combine`: W13 §2,
(Q n^{g₁})^{o₁}(Q n^{g₂})^{o₂} ⊆ (Q n^g)^o anywhere in the prefix, with g ≥ max(g₁,g₂), o ≥ o₂,
the outer constraint o₁ dropped and the kernel exponent possibly raised; `split`: the converse,
(Q n^g)^o ⊆ (Q n^{g₁})^{o₁}(Q n^{g₂})^{o₂} with o₂ ≥ o and g₁, g₂, o₁ arbitrary. -/
inductive WStepX (c : ℝ) : WLine → WLine → Prop
  | speed (bl : List Blk) (k : Bool) (a x g g₂ o₁ o₂ a₂ : ℝ) (hx : 0 ≤ x) (hg : x ≤ g)
      (hg₂ : 0 ≤ g₂) (h₁ : max (pin bl) x ≤ o₁) (h₂ : pin bl ≤ o₂) (h₃ : a - x ≤ a₂) :
      WStepX c (bl, k, a) (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: bl, k, a₂)
  | speedMerge (u : Blk) (rest : List Blk) (k : Bool) (a x g g₂ o₁ o₂ a₂ : ℝ) (hq : u.q = k)
      (hx : 0 ≤ x) (hg : max u.g x ≤ g) (hg₂ : 0 ≤ g₂) (h₁ : max u.o x ≤ o₁) (h₂ : u.o ≤ o₂)
      (h₃ : a - x ≤ a₂) :
      WStepX c (u :: rest, k, a) (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: rest, k, a₂)
  | pop (u : Blk) (rest : List Blk) (k : Bool) (a e : ℝ) (hq : u.q = k)
      (h : c * max (max u.g a) (max u.o (pin rest)) ≤ e) : WStepX c (u :: rest, k, a) (rest, !k, e)
  | flip (u : Blk) (rest : List Blk) (k : Bool) (a e : ℝ) (h : c * max a u.o ≤ e) :
      WStepX c (u :: rest, k, a) (u :: rest, !k, e)
  | flipQ (k : Bool) (a e : ℝ) (h : c * max a 1 ≤ e) : WStepX c ([], k, a) ([], !k, e)
  | combine (bl bl' pre post : List Blk) (u₁ u₂ w : Blk) (k : Bool) (a a' : ℝ)
      (hbl : bl = pre ++ u₂ :: u₁ :: post) (hbl' : bl' = pre ++ w :: post) (h₁ : u₁.q = u₂.q)
      (hw : w.q = u₂.q) (hg : max u₁.g u₂.g ≤ w.g) (ho : u₂.o ≤ w.o) (ha : a ≤ a') :
      WStepX c (bl, k, a) (bl', k, a')
  | split (bl bl' pre post : List Blk) (w u₁ u₂ : Blk) (k : Bool) (a a' : ℝ)
      (hbl : bl = pre ++ w :: post) (hbl' : bl' = pre ++ u₂ :: u₁ :: post) (h₁ : u₁.q = w.q)
      (h₂ : u₂.q = w.q) (ho : w.o ≤ u₂.o) (ha : a ≤ a') :
      WStepX c (bl, k, a) (bl', k, a')

/-- The exact extended calculus: `WStepE` plus the exact values of the non-merging speedup
(Lemma 6.1 with b the input constraint of the innermost block), the matching-kernel flip
Q(∃n^g)^o NTS[n^a] ⊆ Q(∃n^g)^o coNTS[n^{c·max(a,o)}], the quantifier-free flip, and the identity
of W13 §2, (Q n^a)^a (Q n^b)^b K = (Q n^{max(a,b)})^b K, in both directions, anywhere in the
prefix. -/
inductive WStepXE (c : ℝ) : WLine → WLine → Prop
  | base {L L' : WLine} (h : WStepE c L L') : WStepXE c L L'
  | speedSame (u : Blk) (rest : List Blk) (k : Bool) (a x : ℝ) (hq : u.q = k) (hb : 1 ≤ u.o)
      (ha : 1 ≤ a) (hx : 0 ≤ x) :
      WStepXE c (u :: rest, k, a) (⟨!k, 0, u.o⟩ :: ⟨k, x, max u.o x⟩ :: u :: rest, k, a - x)
  | flipM (u : Blk) (rest : List Blk) (k : Bool) (a : ℝ) (hq : u.q = k) :
      WStepXE c (u :: rest, k, a) (u :: rest, !k, c * max a u.o)
  | flipQ (k : Bool) (a : ℝ) : WStepXE c ([], k, a) ([], !k, c * max a 1)
  | combine (pre post : List Blk) (q k : Bool) (a b e : ℝ) :
      WStepXE c (pre ++ ⟨q, b, b⟩ :: ⟨q, a, a⟩ :: post, k, e) (pre ++ ⟨q, max a b, b⟩ :: post, k, e)
  | split (pre post : List Blk) (q k : Bool) (a b e : ℝ) :
      WStepXE c (pre ++ ⟨q, max a b, b⟩ :: post, k, e) (pre ++ ⟨q, b, b⟩ :: ⟨q, a, a⟩ :: post, k, e)

theorem wstepE_wstep {c : ℝ} {L L' : WLine} (h : WStepE c L L') : WStep c L L' := by
  cases h with
  | speedNew bl k a x hq hb ha hx =>
    exact WStep.speedNew bl k a x x 0 _ _ _ hq hx le_rfl le_rfl le_rfl le_rfl le_rfl
  | speedMerge u rest k a x hq hb ha hx =>
    exact WStep.speedMerge u rest k a x _ 0 _ _ _ hq hx le_rfl le_rfl le_rfl le_rfl le_rfl
  | pop u rest k a hq => exact WStep.pop u rest k a _ hq le_rfl
  | flip u rest k a hq => exact WStep.flip u rest k a _ hq le_rfl

theorem wstep_wstepX {c : ℝ} {L L' : WLine} (h : WStep c L L') : WStepX c L L' := by
  cases h with
  | speedNew bl k a x g g₂ o₁ o₂ a₂ _ hx hg hg₂ h₁ h₂ h₃ =>
    exact WStepX.speed bl k a x g g₂ o₁ o₂ a₂ hx hg hg₂ h₁ h₂ h₃
  | speedMerge u rest k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃ =>
    exact WStepX.speedMerge u rest k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃
  | pop u rest k a e hq h => exact WStepX.pop u rest k a e hq h
  | flip u rest k a e _ h => exact WStepX.flip u rest k a e h

theorem wstepXE_wstepX {c : ℝ} {L L' : WLine} (h : WStepXE c L L') : WStepX c L L' := by
  cases h with
  | base h => exact wstep_wstepX (wstepE_wstep h)
  | speedSame u rest k a x _ _ _ hx =>
    exact WStepX.speed (u :: rest) k a x x 0 _ _ _ hx le_rfl le_rfl le_rfl le_rfl le_rfl
  | flipM u rest k a _ => exact WStepX.flip u rest k a _ le_rfl
  | flipQ k a => exact WStepX.flipQ k a _ le_rfl
  | combine pre post q k a b e =>
    exact WStepX.combine _ _ pre post _ _ _ k e e rfl rfl rfl rfl (by simp) le_rfl le_rfl
  | split pre post q k a b e =>
    exact WStepX.split _ _ pre post _ _ _ k e e rfl rfl rfl rfl le_rfl le_rfl

/-! ### Encoding into the reduced system -/

def mflag (bl : List Blk) (k : Bool) : Bool :=
  match bl with
  | [] => true
  | u :: _ => decide (u.q = k)

/-- Input constraint clamped at 0. -/
noncomputable def oc (u : Blk) : ℝ := max u.o 0

/-- Entries of the runs outside a block of type `q`, innermost first; blocks of type `q` directly
outside it belong to its run and are skipped. -/
noncomputable def rrT (q : Bool) : List Blk → List ℝ
  | [] => []
  | v :: rest => if v.q = q then rrT q rest else oc v :: rrT v.q rest

/-- One entry per maximal run of adjacent same-type blocks, innermost first: the clamped input
constraint of the innermost block of the run. -/
noncomputable def rr : List Blk → List ℝ
  | [] => []
  | u :: rest => oc u :: rrT u.q rest

/-- Run entries outermost first, "kernel matches the innermost block", kernel clamped at 0. -/
noncomputable def enc (L : WLine) : TLine := ((rr L.1).reverse, mflag L.1 L.2.1, max L.2.2 0)

theorem rrT_same {q : Bool} {v : Blk} (rest : List Blk) (hv : v.q = q) :
    rrT q (v :: rest) = rrT q rest := by simp [rrT, hv]

theorem rrT_diff {q : Bool} {v : Blk} (rest : List Blk) (hv : v.q ≠ q) :
    rrT q (v :: rest) = oc v :: rrT v.q rest := by simp [rrT, hv]

/-- Dropping the outer one of two adjacent same-type blocks does not change the run entries. -/
theorem rrT_drop {u₁ u₂ : Blk} (post : List Blk) (h : u₁.q = u₂.q) :
    ∀ (pre : List Blk) (q : Bool), rrT q (pre ++ u₂ :: u₁ :: post) = rrT q (pre ++ u₂ :: post)
  | [], q => by
    simp only [List.nil_append]
    by_cases hu : u₂.q = q
    · rw [rrT_same _ hu, rrT_same _ (h.trans hu), rrT_same _ hu]
    · rw [rrT_diff _ hu, rrT_diff _ hu, rrT_same _ h]
  | p :: pre, q => by
    simp only [List.cons_append]
    by_cases hp : p.q = q
    · rw [rrT_same _ hp, rrT_same _ hp, rrT_drop post h pre q]
    · rw [rrT_diff _ hp, rrT_diff _ hp, rrT_drop post h pre p.q]

theorem rr_drop {u₁ u₂ : Blk} (pre post : List Blk) (h : u₁.q = u₂.q) :
    rr (pre ++ u₂ :: u₁ :: post) = rr (pre ++ u₂ :: post) := by
  cases pre with
  | nil => simp only [List.nil_append, rr]; rw [rrT_same _ h]
  | cons p pre => simp only [List.cons_append, rr]; rw [rrT_drop post h pre p.q]

theorem f2_refl : ∀ l : List ℝ, List.Forall₂ (· ≤ ·) l l
  | [] => List.Forall₂.nil
  | _ :: l => List.Forall₂.cons le_rfl (f2_refl l)

/-- Raising the constraint of a block raises at most one run entry. -/
theorem rrT_mono {u w : Blk} (post : List Blk) (hq : w.q = u.q) (ho : oc u ≤ oc w) :
    ∀ (pre : List Blk) (q : Bool),
      List.Forall₂ (· ≤ ·) (rrT q (pre ++ u :: post)) (rrT q (pre ++ w :: post))
  | [], q => by
    simp only [List.nil_append]
    by_cases hu : u.q = q
    · rw [rrT_same _ hu, rrT_same _ (hq.trans hu)]; exact f2_refl _
    · rw [rrT_diff _ hu, rrT_diff _ (by rw [hq]; exact hu), hq]
      exact List.Forall₂.cons ho (f2_refl _)
  | p :: pre, q => by
    simp only [List.cons_append]
    by_cases hp : p.q = q
    · rw [rrT_same _ hp, rrT_same _ hp]; exact rrT_mono post hq ho pre q
    · rw [rrT_diff _ hp, rrT_diff _ hp]
      exact List.Forall₂.cons le_rfl (rrT_mono post hq ho pre p.q)

theorem rr_mono {u w : Blk} (pre post : List Blk) (hq : w.q = u.q) (ho : oc u ≤ oc w) :
    List.Forall₂ (· ≤ ·) (rr (pre ++ u :: post)) (rr (pre ++ w :: post)) := by
  cases pre with
  | nil => simp only [List.nil_append, rr]; rw [hq]; exact List.Forall₂.cons ho (f2_refl _)
  | cons p pre =>
    simp only [List.cons_append, rr]
    exact List.Forall₂.cons le_rfl (rrT_mono post hq ho pre p.q)

theorem f2_getD {l l' : List ℝ} (h : List.Forall₂ (· ≤ ·) l l') : ∀ i, l.getD i 0 ≤ l'.getD i 0 := by
  induction h with
  | nil => intro i; exact le_rfl
  | cons hxy _ ih =>
    intro i
    cases i with
    | zero => simpa using hxy
    | succ i => simpa using ih i

theorem weak_f2 {c : ℝ} {l l' : List ℝ} (h : List.Forall₂ (· ≤ ·) l l') (t : Bool) {a a' : ℝ}
    (ha : a ≤ a') : TStep c (l.reverse, t, a) (l'.reverse, t, a') :=
  TStep.weak _ _ t a a' (by simp [h.length_eq]) (f2_getD (List.forall₂_reverse_iff.mpr h)) ha

theorem mflag_app {u v : Blk} (pre r s : List Blk) (k : Bool) (h : v.q = u.q) :
    mflag (pre ++ u :: r) k = mflag (pre ++ v :: s) k := by
  cases pre <;> simp [mflag, h]

theorem clamp_sub {a x a₂ : ℝ} (hx : 0 ≤ x) (h : a - x ≤ a₂) :
    max a 0 - min x (max a 0) ≤ max a₂ 0 := by
  rcases le_total x (max a 0) with hm | hm
  · rw [min_eq_left hm]
    rcases le_total a 0 with ha | ha
    · rw [max_eq_right ha]; linarith [le_max_right a₂ 0]
    · rw [max_eq_left ha]; linarith [le_max_left a₂ 0]
  · rw [min_eq_right hm, sub_self]; exact le_max_right _ _

theorem cmax_le {c X Y e : ℝ} (hc : 0 ≤ c) (hXY : X ≤ max Y 0) (he : c * Y ≤ e) :
    c * X ≤ max e 0 := by
  rcases le_total Y 0 with hY | hY
  · rw [max_eq_right hY] at hXY
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos hc hXY) (le_max_right _ _)
  · rw [max_eq_left hY] at hXY
    exact le_trans (le_trans (mul_le_mul_of_nonneg_left hXY hc) he) (le_max_left _ _)

theorem top_nil : top ([] : List ℝ) = 0 := rfl

theorem decide_not_eq (q k : Bool) : decide (q = !k) = !decide (q = k) := by
  cases q <;> cases k <;> rfl

theorem enc_cons (u : Blk) (rest : List Blk) (k : Bool) (a : ℝ) :
    enc (u :: rest, k, a) = ((rrT u.q rest).reverse ++ [oc u], decide (u.q = k), max a 0) := by
  simp [enc, rr, mflag]

theorem top_rev_cons (x : ℝ) (l : List ℝ) : top (x :: l).reverse = x := by
  rw [List.reverse_cons, top_concat]

theorem max3_le {p q r Y : ℝ} (hp : p ≤ Y) (hq : q ≤ Y) (hr : r ≤ Y) :
    max p (max (max q 0) (max r 0)) ≤ max Y 0 :=
  max_le (le_trans hp (le_max_left _ _))
    (max_le (max_le_max hq le_rfl) (max_le_max hr le_rfl))

theorem max3_le' {p q r Y : ℝ} (hp : p ≤ Y) (hq : q ≤ Y) (hr : r ≤ Y) :
    max (max p 0) (max (max q 0) (max r 0)) ≤ max Y 0 :=
  max_le (max_le_max hp le_rfl) (max_le (max_le_max hq le_rfl) (max_le_max hr le_rfl))

theorem speed_ok {x a o b o₁ : ℝ} (hb : max b x ≤ o₁) (ho : o ≤ b) :
    max (min x (max a 0)) (max o 0) ≤ max o₁ 0 :=
  max_le (le_trans (min_le_left _ _) (le_trans (le_trans (le_max_right _ _) hb) (le_max_left _ _)))
    (max_le_max (le_trans ho (le_trans (le_max_left _ _) hb)) le_rfl)

/-- **Simulation lemma, nonempty prefix.** One `WStepX` step is one reduced step. Lines need not
alternate. -/
theorem sim {c : ℝ} (hc : 0 ≤ c) {L L' : WLine} (h : WStepX c L L') (hne : L.1 ≠ []) :
    TStep c (enc L) (enc L') := by
  cases h with
  | speed bl k a x g g₂ o₁ o₂ a₂ hx hg hg₂ h₁ h₂ h₃ =>
    obtain ⟨u, rest, rfl⟩ : ∃ u rest, bl = u :: rest := by
      cases bl with
      | nil => exact absurd rfl hne
      | cons u rest => exact ⟨u, rest, rfl⟩
    simp only [pin] at h₁ h₂
    have e2 : rr (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: u :: rest) =
        max o₂ 0 :: max o₁ 0 :: rrT k (u :: rest) := by
      simp [rr, rrT, oc]
    have hm : mflag (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: u :: rest) k = false := by simp [mflag]
    by_cases hq : u.q = k
    · have e1 : enc (u :: rest, k, a) = ((rrT k rest).reverse ++ [oc u], true, max a 0) := by
        rw [enc_cons, hq]; simp
      have e2' : enc (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: u :: rest, k, a₂) =
          ((rrT k rest).reverse ++ [max o₁ 0, max o₂ 0], false, max a₂ 0) := by
        simp only [enc, e2, hm, rrT_same _ hq]; simp
      rw [e1, e2']
      exact TStep.speedM _ (oc u) (max a 0) (min x (max a 0)) _ _ (max a₂ 0)
        (le_min hx (le_max_right _ _)) (min_le_right _ _) (speed_ok h₁ le_rfl)
        (max_le_max h₂ le_rfl) (clamp_sub hx h₃)
    · have e2' : enc (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: u :: rest, k, a₂) =
          ((rrT u.q rest).reverse ++ [oc u, max o₁ 0, max o₂ 0], false, max a₂ 0) := by
        simp only [enc, e2, hm, rrT_diff _ hq]; simp
      rw [enc_cons, e2']
      exact TStep.speedO _ (oc u) (max a 0) (min x (max a 0)) _ _ (max a₂ 0)
        (le_min hx (le_max_right _ _)) (min_le_right _ _) (speed_ok h₁ le_rfl)
        (max_le_max h₂ le_rfl) (clamp_sub hx h₃)
  | speedMerge u rest k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃ =>
    have e1 : enc (u :: rest, k, a) = ((rrT k rest).reverse ++ [oc u], true, max a 0) := by
      rw [enc_cons, hq]; simp
    have e2 : enc (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: rest, k, a₂) =
        ((rrT k rest).reverse ++ [max o₁ 0, max o₂ 0], false, max a₂ 0) := by
      simp [enc, rr, rrT, oc, mflag]
    rw [e1, e2]
    exact TStep.speedM _ (oc u) (max a 0) (min x (max a 0)) _ _ (max a₂ 0)
      (le_min hx (le_max_right _ _)) (min_le_right _ _) (speed_ok h₁ le_rfl)
      (max_le_max h₂ le_rfl) (clamp_sub hx h₃)
  | pop u rest k a e hq hcost =>
    have e1 : enc (u :: rest, k, a) = ((rrT k rest).reverse ++ [oc u], true, max a 0) := by
      rw [enc_cons, hq]; simp
    rw [e1]
    cases rest with
    | nil =>
      simp only [pin] at hcost
      have e2 : enc ([], !k, e) = ([], true, max e 0) := by simp [enc, rr, mflag]
      rw [e2]
      refine TStep.pop _ (oc u) (max a 0) (max e 0) (cmax_le hc ?_ hcost)
      simp only [rrT, List.reverse_nil, top_nil]
      exact max3_le (le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_right _ _)))
        (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) (le_max_left _ _))
    | cons v r =>
      simp only [pin] at hcost
      have hX : max (oc v) (max (oc u) (max a 0)) ≤ max (max (max u.g a) (max u.o v.o)) 0 :=
        max3_le' (le_trans (le_max_right _ _) (le_max_right _ _))
          (le_trans (le_max_left _ _) (le_max_right _ _))
          (le_trans (le_max_right _ _) (le_max_left _ _))
      by_cases hv : v.q = k
      · have e2 : enc (v :: r, !k, e) = ((rrT k r).reverse ++ [oc v], false, max e 0) := by
          rw [enc_cons, hv]; simp
        rw [rrT_same _ hv, e2]
        exact TStep.popIn _ (oc u) (oc v) (max a 0) (max e 0) (le_max_right _ _)
          (cmax_le hc hX hcost)
      · have e2 : enc (v :: r, !k, e) = ((rr (v :: r)).reverse, mflag (v :: r) !k, max e 0) := rfl
        rw [rrT_diff _ hv, e2]
        refine TStep.pop _ (oc u) (max a 0) (max e 0) (cmax_le hc ?_ hcost)
        rw [top_rev_cons]
        exact hX
  | flip u rest k a e hcost =>
    have e2 : enc (u :: rest, !k, e) =
        ((rrT u.q rest).reverse ++ [oc u], !decide (u.q = k), max e 0) := by
      rw [enc_cons, decide_not_eq]
    rw [enc_cons, e2]
    refine TStep.flip _ (oc u) (max a 0) (max e 0) _ (cmax_le hc ?_ hcost)
    exact max_le (max_le_max (le_max_right _ _) le_rfl) (max_le_max (le_max_left _ _) le_rfl)
  | flipQ => exact absurd rfl hne
  | combine bl bl' pre post u₁ u₂ w k a a' hbl hbl' h₁ hw hg ho ha =>
    subst hbl hbl'
    simp only [enc]
    rw [rr_drop pre post h₁, mflag_app pre (u₁ :: post) post k hw]
    exact weak_f2 (rr_mono pre post hw (max_le_max ho le_rfl)) _ (max_le_max ha le_rfl)
  | split bl bl' pre post w u₁ u₂ k a a' hbl hbl' h₁ h₂ ho ha =>
    subst hbl hbl'
    simp only [enc]
    rw [rr_drop pre post (h₁.trans h₂.symm), mflag_app pre post (u₁ :: post) k h₂]
    exact weak_f2 (rr_mono pre post h₂ (max_le_max ho le_rfl)) _ (max_le_max ha le_rfl)

/-- **Simulation lemma, empty prefix.** A `WStepX` step from a quantifier-free line to a line
that is not quantifier-free is `init` followed by this reduced step. -/
theorem sim0 {c : ℝ} {L L' : WLine} (h : WStepX c L L') (he : L.1 = []) (hne' : L'.1 ≠ []) :
    TStep c ([0], true, max L.2.2 0) (enc L') := by
  obtain ⟨bl, k, a⟩ := L
  simp only at he
  subst he
  cases h with
  | speed bl k a x g g₂ o₁ o₂ a₂ hx hg hg₂ h₁ h₂ h₃ =>
    have e2 : enc (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: [], k, a₂) =
        ([] ++ [max o₁ 0, max o₂ 0], false, max a₂ 0) := by
      simp [enc, rr, rrT, oc, mflag]
    rw [e2]
    simp only [pin] at h₁ h₂
    exact TStep.speedM [] 0 (max a 0) (min x (max a 0)) _ _ (max a₂ 0)
      (le_min hx (le_max_right _ _)) (min_le_right _ _)
      (max_le (le_trans (min_le_left _ _) (le_trans (le_trans (le_max_right _ _) h₁)
        (le_max_left _ _))) (le_max_right _ _))
      (le_max_right _ _) (clamp_sub hx h₃)
  | flipQ => exact absurd rfl hne'
  | combine bl bl' pre post u₁ u₂ w k a a' hbl => simp at hbl
  | split bl bl' pre post w u₁ u₂ k a a' hbl => simp at hbl

theorem enc_nil {L : WLine} (he : L.1 = []) : enc L = ([], true, max L.2.2 0) := by
  obtain ⟨bl, k, a⟩ := L
  simp only at he
  subst he
  simp [enc, rr, mflag]

theorem enc_ne {L : WLine} (hne : L.1 ≠ []) : (enc L).1 ≠ [] := by
  obtain ⟨bl, k, a⟩ := L
  cases bl with
  | nil => exact absurd rfl hne
  | cons u rest => simp [enc, rr]

/-! ### Invariants of the literal calculus -/

/-- A step between two quantifier-free lines is a quantifier-free flip. -/
theorem step_nil_nil {c : ℝ} {L L' : WLine} (h : WStepX c L L') (he : L.1 = []) (he' : L'.1 = []) :
    L'.2.1 = !L.2.1 ∧ c * max L.2.2 1 ≤ L'.2.2 := by
  cases h with
  | speed => simp at he'
  | speedMerge => simp at he
  | pop => simp at he
  | flip => simp at he
  | flipQ k a e h => exact ⟨rfl, h⟩
  | combine _ _ _ _ _ _ _ _ _ _ hbl => subst hbl; simp at he
  | split _ _ _ _ _ _ _ _ _ _ hbl => subst hbl; simp at he

theorem pop_pos {c : ℝ} (hc : 0 ≤ c) {L L' : WLine} (h : WStepX c L L') (he : L'.1 = []) :
    c ≤ L'.2.2 := by
  cases h with
  | speed => simp at he
  | speedMerge => simp at he
  | flip => simp at he
  | pop u rest k a e hq hcost =>
    simp only at he
    subst he
    simp only [pin] at hcost
    have h1 : (1 : ℝ) ≤ max (max u.g a) (max u.o 1) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * max (max u.g a) (max u.o 1) := mul_le_mul_of_nonneg_left h1 hc
      _ ≤ e := hcost
  | flipQ k a e h =>
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * max a 1 := mul_le_mul_of_nonneg_left (le_max_right _ _) hc
      _ ≤ e := h
  | combine _ _ _ _ _ _ _ _ _ _ _ hbl' => subst hbl'; simp at he
  | split _ _ _ _ _ _ _ _ _ _ _ hbl' => subst hbl'; simp at he

def outer (bl : List Blk) : Option Bool := bl.getLast?.map Blk.q

theorem outer_cons2 (x y : Blk) (l : List Blk) : outer (x :: y :: l) = outer (y :: l) := by
  simp [outer, List.getLast?_cons_cons]

theorem outer_append (pre : List Blk) (x : Blk) (rest : List Blk) :
    outer (pre ++ x :: rest) = outer (x :: rest) := by
  induction pre with
  | nil => rfl
  | cons p pre ih =>
    rw [List.cons_append, ← ih]
    obtain ⟨y, l, hl⟩ : ∃ y l, pre ++ x :: rest = y :: l := by
      cases pre with
      | nil => exact ⟨x, rest, rfl⟩
      | cons y l => exact ⟨y, l ++ x :: rest, rfl⟩
    rw [hl, outer_cons2]

theorem outer_step {c : ℝ} {L L' : WLine} (h : WStepX c L L') (hne : L.1 ≠ []) (hne' : L'.1 ≠ []) :
    outer L'.1 = outer L.1 := by
  cases h with
  | speed bl k a x g g₂ o₁ o₂ a₂ =>
    cases bl with
    | nil => exact absurd rfl hne
    | cons u rest => simp only; rw [outer_cons2, outer_cons2]
  | speedMerge u rest k a x g g₂ o₁ o₂ a₂ hq =>
    simp only; rw [outer_cons2]
    cases rest with
    | nil => simp [outer, hq]
    | cons v r => rw [outer_cons2, outer_cons2]
  | pop u rest k a e hq =>
    cases rest with
    | nil => exact absurd rfl hne'
    | cons v r => simp only; rw [outer_cons2]
  | flip => rfl
  | flipQ => exact absurd rfl hne
  | combine bl bl' pre post u₁ u₂ w k a a' hbl hbl' h₁ hw =>
    subst hbl hbl'
    simp only
    rw [outer_append, outer_append, outer_cons2]
    cases post with
    | nil => simp [outer, h₁, hw]
    | cons v r => rw [outer_cons2, outer_cons2]
  | split bl bl' pre post w u₁ u₂ k a a' hbl hbl' h₁ =>
    subst hbl hbl'
    simp only
    rw [outer_append, outer_append, outer_cons2]
    cases post with
    | nil => simp [outer, h₁]
    | cons v r => rw [outer_cons2, outer_cons2]

/-! ### Complementation -/

def cblk (u : Blk) : Blk := ⟨!u.q, u.g, u.o⟩

def compl (L : WLine) : WLine := (L.1.map cblk, !L.2.1, L.2.2)

theorem pin_map (bl : List Blk) : pin (bl.map cblk) = pin bl := by
  cases bl <;> rfl

theorem compl_compl (L : WLine) : compl (compl L) = L := by
  obtain ⟨bl, k, a⟩ := L
  simp only [compl, List.map_map, Bool.not_not]
  congr 1
  conv_rhs => rw [← List.map_id bl]
  apply List.map_congr_left
  intro u _
  simp [cblk]

theorem outer_map (bl : List Blk) : outer (bl.map cblk) = (outer bl).map (fun b => !b) := by
  simp [outer, List.getLast?_map, Option.map_map]
  rfl

theorem wstep_compl {c : ℝ} {L L' : WLine} (h : WStep c L L') : WStep c (compl L) (compl L') := by
  cases h with
  | speedNew bl k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃ =>
    have := WStep.speedNew (c := c) (bl.map cblk) (!k) a x g g₂ o₁ o₂ a₂
      (fun u rest he => by
        cases bl with
        | nil => simp at he
        | cons u₀ r₀ =>
          simp only [List.map_cons, List.cons.injEq] at he
          rw [← he.1]; simp [cblk]; exact hq u₀ r₀ rfl)
      hx hg hg₂ (by rw [pin_map]; exact h₁) (by rw [pin_map]; exact h₂) h₃
    simpa [compl, cblk] using this
  | speedMerge u rest k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃ =>
    have := WStep.speedMerge (c := c) (cblk u) (rest.map cblk) (!k) a x g g₂ o₁ o₂ a₂
      (by simp [cblk, hq]) hx hg hg₂ h₁ h₂ h₃
    simpa [compl, cblk] using this
  | pop u rest k a e hq hcost =>
    have := WStep.pop (c := c) (cblk u) (rest.map cblk) (!k) a e (by simp [cblk, hq])
      (by rw [pin_map]; exact hcost)
    simpa [compl, cblk] using this
  | flip u rest k a e hq hcost =>
    have := WStep.flip (c := c) (cblk u) (rest.map cblk) (!k) a e (by simp [cblk]; exact hq) hcost
    simpa [compl, cblk] using this

theorem wstepE_compl {c : ℝ} {L L' : WLine} (h : WStepE c L L') : WStepE c (compl L) (compl L') := by
  cases h with
  | speedNew bl k a x hq hb ha hx =>
    have := WStepE.speedNew (c := c) (bl.map cblk) (!k) a x
      (fun u rest he => by
        cases bl with
        | nil => simp at he
        | cons u₀ r₀ =>
          simp only [List.map_cons, List.cons.injEq] at he
          rw [← he.1]; simp [cblk]; exact hq u₀ r₀ rfl)
      (by rw [pin_map]; exact hb) ha hx
    simpa [compl, cblk, pin_map] using this
  | speedMerge u rest k a x hq hb ha hx =>
    have := WStepE.speedMerge (c := c) (cblk u) (rest.map cblk) (!k) a x (by simp [cblk, hq]) hb ha hx
    simpa [compl, cblk] using this
  | pop u rest k a hq =>
    have := WStepE.pop (c := c) (cblk u) (rest.map cblk) (!k) a (by simp [cblk, hq])
    simpa [compl, cblk, pin_map] using this
  | flip u rest k a hq =>
    have := WStepE.flip (c := c) (cblk u) (rest.map cblk) (!k) a (by simp [cblk]; exact hq)
    simpa [compl, cblk] using this

theorem wstepX_compl {c : ℝ} {L L' : WLine} (h : WStepX c L L') : WStepX c (compl L) (compl L') := by
  cases h with
  | speed bl k a x g g₂ o₁ o₂ a₂ hx hg hg₂ h₁ h₂ h₃ =>
    have := WStepX.speed (c := c) (bl.map cblk) (!k) a x g g₂ o₁ o₂ a₂ hx hg hg₂
      (by rw [pin_map]; exact h₁) (by rw [pin_map]; exact h₂) h₃
    simpa [compl, cblk] using this
  | speedMerge u rest k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃ =>
    have := WStepX.speedMerge (c := c) (cblk u) (rest.map cblk) (!k) a x g g₂ o₁ o₂ a₂
      (by simp [cblk, hq]) hx hg hg₂ h₁ h₂ h₃
    simpa [compl, cblk] using this
  | pop u rest k a e hq hcost =>
    have := WStepX.pop (c := c) (cblk u) (rest.map cblk) (!k) a e (by simp [cblk, hq])
      (by rw [pin_map]; exact hcost)
    simpa [compl, cblk] using this
  | flip u rest k a e hcost =>
    have := WStepX.flip (c := c) (cblk u) (rest.map cblk) (!k) a e hcost
    simpa [compl, cblk] using this
  | flipQ k a e h =>
    have := WStepX.flipQ (c := c) (!k) a e h
    simpa [compl] using this
  | combine bl bl' pre post u₁ u₂ w k a a' hbl hbl' h₁ hw hg ho ha =>
    subst hbl hbl'
    have := WStepX.combine (c := c) _ _ (pre.map cblk) (post.map cblk) (cblk u₁) (cblk u₂)
      (cblk w) (!k) a a' rfl rfl (by simp [cblk, h₁]) (by simp [cblk, hw]) hg ho ha
    simpa [compl] using this
  | split bl bl' pre post w u₁ u₂ k a a' hbl hbl' h₁ h₂ ho ha =>
    subst hbl hbl'
    have := WStepX.split (c := c) _ _ (pre.map cblk) (post.map cblk) (cblk w) (cblk u₁)
      (cblk u₂) (!k) a a' rfl rfl (by simp [cblk, h₁]) (by simp [cblk, h₂]) ho ha
    simpa [compl] using this

/-! ### Paths, segments, normal form -/

def Path (R : WLine → WLine → Prop) (M : ℕ → WLine) (n : ℕ) : Prop := ∀ i < n, R (M i) (M (i + 1))

/-- W13 Definition 6.4 (normal form), in the calculus `R`: first line NTS[n^a], last line
coNTS[n^{a'}] with a' ≤ a, at least two lines, no other quantifier-free line; the first line is
a simple class. -/
def NF (R : WLine → WLine → Prop) (M : ℕ → WLine) (n : ℕ) : Prop :=
  1 ≤ n ∧ Path R M n ∧ (M 0).1 = [] ∧ (M 0).2.1 = true ∧ (M n).1 = [] ∧ (M n).2.1 = false ∧
    (∀ i, 0 < i → i < n → (M i).1 ≠ []) ∧ (M n).2.2 ≤ (M 0).2.2

/-- Outer quantifier is constant along a stretch of quantified lines. -/
theorem stretch_outer {c : ℝ} (M : ℕ → WLine) (p : ℕ) :
    ∀ j, (∀ i, p ≤ i → i < p + j → WStepX c (M i) (M (i + 1))) →
      (∀ i, p ≤ i → i ≤ p + j → (M i).1 ≠ []) → outer (M (p + j)).1 = outer (M p).1 := by
  intro j
  induction j with
  | zero => intro _ _; rfl
  | succ j ih =>
    intro hs hne
    rw [← ih (fun i h1 h2 => hs i h1 (by omega)) (fun i h1 h2 => hne i h1 (by omega))]
    rw [show p + (j + 1) = p + j + 1 by omega]
    exact outer_step (hs (p + j) (by omega) (by omega)) (hne _ (by omega) (by omega))
      (hne _ (by omega) (by omega))

/-- In a segment between quantifier-free lines the kernel type flips (NTS → coNTS or back). -/
theorem seg_types {c : ℝ} {M : ℕ → WLine} {n : ℕ} (hn : 1 ≤ n) (hp : Path (WStepX c) M n)
    (h0 : (M 0).1 = []) (hN : (M n).1 = []) (hmid : ∀ i, 0 < i → i < n → (M i).1 ≠ []) :
    (M n).2.1 = !(M 0).2.1 := by
  rcases Nat.lt_or_ge n 2 with h1 | hn2
  · obtain rfl : n = 1 := by omega
    exact (step_nil_nil (hp 0 (by omega)) h0 hN).1
  have ho1 : outer (M 1).1 = some (M 0).2.1 := by
    have h01 := hp 0 (by omega)
    have hne1 := hmid 1 (by omega) (by omega)
    simp only [Nat.zero_add] at h01
    generalize M 0 = A at h01 h0 ⊢
    generalize M 1 = B at h01 hne1 ⊢
    obtain ⟨bl, k, a⟩ := A
    simp only at h0
    subst h0
    cases h01 with
    | speed bl k a x g g₂ o₁ o₂ a₂ => simp [outer]
    | flipQ => exact absurd rfl hne1
    | combine _ _ _ _ _ _ _ _ _ _ hbl => simp at hbl
    | split _ _ _ _ _ _ _ _ _ _ hbl => simp at hbl
  have hst := stretch_outer (c := c) M 1 (n - 2) (fun i h1 h2 => hp i (by omega))
    (fun i h1 h2 => hmid i (by omega) (by omega))
  rw [show 1 + (n - 2) = n - 1 by omega, ho1] at hst
  have hlast := hp (n - 1) (by omega)
  have hne := hmid (n - 1) (by omega) (by omega)
  rw [show n - 1 + 1 = n by omega] at hlast
  generalize M (n - 1) = A at hst hlast hne
  generalize M n = B at hlast hN ⊢
  obtain ⟨bl, k, a⟩ := A
  obtain ⟨bl', k', a'⟩ := B
  simp only at hN hst hne ⊢
  subst hN
  cases hlast with
  | pop u rest k a e hq =>
    simp [outer] at hst
    rw [← hst, hq]
  | flipQ => exact absurd rfl hne
  | combine _ _ _ _ _ _ _ _ _ _ _ hbl' => simp at hbl'
  | split _ _ _ _ _ _ _ _ _ _ _ hbl' => simp at hbl'

/-- W13 Lemma 6.5-level map: a normal-form `WStepX` proof with at least two steps gives a
`TRefutes` instance. -/
theorem nf_trefutes {c : ℝ} (hc : 0 < c) {M : ℕ → WLine} {n : ℕ} (hn : 2 ≤ n)
    (hp : Path (WStepX c) M n) (h0 : (M 0).1 = []) (hN : (M n).1 = [])
    (hmid : ∀ i, 0 < i → i < n → (M i).1 ≠ []) (hle : (M n).2.2 ≤ (M 0).2.2) :
    ∃ T, TRefutes c (n + 1) T := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpos : c ≤ (M (m + 1)).2.2 := pop_pos hc.le (hp m (by omega)) hN
  have ha0 : 0 < (M 0).2.2 := by linarith
  let T : ℕ → TLine := fun i =>
    match i with
    | 0 => enc (M 0)
    | 1 => ([0], true, max (M 0).2.2 0)
    | j + 2 => enc (M (j + 1))
  refine ⟨T, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (enc (M 0)).1 = []; rw [enc_nil h0]
  · show (enc (M (m + 1))).1 = []; rw [enc_nil hN]
  · show 0 < (enc (M 0)).2.2; rw [enc_nil h0]; exact lt_max_of_lt_left ha0
  · show (enc (M (m + 1))).2.2 ≤ (enc (M 0)).2.2
    rw [enc_nil h0, enc_nil hN]; exact max_le_max hle le_rfl
  · intro i hi
    match i, hi with
    | 0, _ => show TStep c (enc (M 0)) _; rw [enc_nil h0]; exact TStep.init _
    | 1, _ => exact sim0 (hp 0 (by omega)) h0 (hmid 1 (by omega) (by omega))
    | j + 2, hj => exact sim hc.le (hp (j + 1) (by omega)) (hmid _ (by omega) (by omega))
  · intro i h1 h2
    match i, h1, h2 with
    | 1, _, _ => simp [T]
    | j + 2, _, hj => exact enc_ne (hmid _ (by omega) (by omega))

/-! Generic part: a calculus `R ⊆ WStepX c` closed under complementation. -/
section generic
variable {c : ℝ} {R : WLine → WLine → Prop}

/-- If no normal-form segment exists, quantifier-free exponents strictly increase along paths. -/
theorem qf_up
    (hseg : ∀ (M : ℕ → WLine) (n : ℕ), 1 ≤ n → Path R M n → (M 0).1 = [] → (M n).1 = [] →
      (∀ i, 0 < i → i < n → (M i).1 ≠ []) → (M 0).2.2 < (M n).2.2) :
    ∀ n (M : ℕ → WLine), 1 ≤ n → Path R M n → (M 0).1 = [] → (M n).1 = [] →
      (M 0).2.2 < (M n).2.2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hn hp h0 hN
  classical
  have hex : ∃ m, 0 < m ∧ m ≤ n ∧ (M m).1 = [] := ⟨n, by omega, le_rfl, hN⟩
  set m := Nat.find hex with hm
  obtain ⟨hm1, hm2, hm3⟩ := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < m → (M i).1 ≠ [] := by
    intro i h1 h2 h3
    exact Nat.find_min hex h2 ⟨h1, by omega, h3⟩
  have hfirst := hseg M m hm1 (fun i hi => hp i (by omega)) h0 hm3 hmin
  rcases Nat.eq_or_lt_of_le hm2 with heq | hlt
  · rw [← heq]; exact hfirst
  · have := ih (n - m) (by omega) (fun i => M (m + i)) (by omega)
      (fun i hi => by
        have := hp (m + i) (by omega)
        rw [show m + i + 1 = m + (i + 1) by omega] at this
        exact this)
      (by simpa using hm3) (by rw [show m + (n - m) = n by omega]; exact hN)
    simp only [Nat.add_zero] at this
    rw [show m + (n - m) = n by omega] at this
    exact lt_trans hfirst this

/-- Without normal-form proofs in `R`, the exponent strictly increases between any two
quantifier-free lines of an `R`-path. -/
theorem qf_strict (hR : ∀ L L', R L L' → WStepX c L L')
    (hRc : ∀ L L', R L L' → R (compl L) (compl L')) (hno : ¬ ∃ M n, NF R M n) :
    ∀ n (M : ℕ → WLine), 1 ≤ n → Path R M n → (M 0).1 = [] → (M n).1 = [] →
      (M 0).2.2 < (M n).2.2 := by
  refine qf_up ?_
  intro M n hn hpM h0 hNM hmid
  by_contra hle
  push Not at hle
  have hty := seg_types hn (fun i hi => hR _ _ (hpM i hi)) h0 hNM hmid
  cases ht : (M 0).2.1 with
  | true =>
    rw [ht] at hty
    exact hno ⟨M, n, hn, hpM, h0, ht, hNM, hty, hmid, hle⟩
  | false =>
    rw [ht] at hty
    refine hno ⟨fun i => compl (M i), n, hn, fun i hi => hRc _ _ (hpM i hi), ?_, ?_, ?_, ?_,
      ?_, hle⟩
    · simp [compl, h0]
    · simp [compl, ht]
    · simp [compl, hNM]
    · simp [compl, hty]
    · intro i h1 h2; simp [compl]; exact hmid i h1 h2

/-- The splice of W13 Theorem 4.4's proof: a proof A ⊆ ¬A, followed by its complement, contains a
path from any quantifier-free line Q on it to ¬Q. -/
theorem splice (hRc : ∀ L L', R L L' → R (compl L) (compl L')) {L : ℕ → WLine} {N : ℕ}
    (hp : Path R L N) (hend : L N = compl (L 0)) {i : ℕ} (hi : i ≤ N) :
    ∃ S : ℕ → WLine, Path R S N ∧ S 0 = L i ∧ S N = compl (L i) := by
  classical
  let D : ℕ → WLine := fun t => if t ≤ N then L t else compl (L (t - N))
  have hD : ∀ t, N ≤ t → D t = compl (L (t - N)) := by
    intro t ht
    rcases Nat.eq_or_lt_of_le ht with h | h
    · subst h; simp [D, hend]
    · simp [D, show ¬ t ≤ N by omega]
  refine ⟨fun t => D (i + t), ?_, ?_, ?_⟩
  · intro t ht
    show R (D (i + t)) (D (i + (t + 1)))
    by_cases h1 : i + t + 1 ≤ N
    · have e1 : D (i + t) = L (i + t) := by simp [D, show i + t ≤ N by omega]
      have e2 : D (i + (t + 1)) = L (i + t + 1) := by
        simp [D, show i + (t + 1) ≤ N by omega]; rfl
      rw [e1, e2]; exact hp _ (by omega)
    · rw [hD _ (by omega), hD _ (by omega), show i + (t + 1) - N = i + t - N + 1 by omega]
      exact hRc _ _ (hp _ (by omega))
  · simp [D, hi]
  · show D (i + N) = compl (L i)
    rw [hD _ (by omega), show i + N - N = i by omega]

/-- Some line of a proof A ⊆ ¬A is quantifier-free. -/
theorem exists_qf (hR : ∀ L L', R L L' → WStepX c L L') {L : ℕ → WLine} {N : ℕ}
    (hp : Path R L N) (hout : outer (L N).1 = outer (compl (L 0)).1) : ∃ i ≤ N, (L i).1 = [] := by
  by_contra hno
  push Not at hno
  have hst := stretch_outer (c := c) L 0 N (fun i _ h2 => hR _ _ (hp i (by omega)))
    (fun i _ h2 => hno i (by omega))
  simp only [Nat.zero_add] at hst
  rw [hout] at hst
  simp only [compl] at hst
  rw [outer_map] at hst
  have hne := hno 0 (by omega)
  obtain ⟨b, hb⟩ : ∃ b, outer (L 0).1 = some b := by
    cases h : (L 0).1.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some u => exact ⟨u.q, by simp [outer, h]⟩
  rw [hb] at hst
  cases b <;> simp at hst

/-- **W13 Theorem 6.6 for the calculus `R`.** A proof that A ⊆ ¬A (A any simple class, at least
two lines) yields a normal-form proof. -/
theorem normal_form_gen (hR : ∀ L L', R L L' → WStepX c L L')
    (hRc : ∀ L L', R L L' → R (compl L) (compl L')) {L : ℕ → WLine} {N : ℕ} (hN : 1 ≤ N)
    (hp : Path R L N) (hend : L N = compl (L 0)) : ∃ M n, NF R M n := by
  by_contra hno
  have hstrict := qf_strict hR hRc hno
  obtain ⟨i, hi, hqf⟩ := exists_qf hR hp (by rw [hend])
  obtain ⟨S, hS, hS0, hSN⟩ := splice hRc hp hend hi
  have := hstrict N S hN hS (by rw [hS0]; exact hqf) (by rw [hSN]; simp [compl, hqf])
  rw [hS0, hSN] at this
  simp [compl] at this

end generic

theorem normal_form {c : ℝ} {L : ℕ → WLine} {N : ℕ} (hN : 1 ≤ N) (hp : Path (WStep c) L N)
    (hend : L N = compl (L 0)) : ∃ M n, NF (WStep c) M n :=
  normal_form_gen (fun _ _ h => wstep_wstepX h) (fun _ _ h => wstep_compl h) hN hp hend

theorem normal_formE {c : ℝ} {L : ℕ → WLine} {N : ℕ} (hN : 1 ≤ N) (hp : Path (WStepE c) L N)
    (hend : L N = compl (L 0)) : ∃ M n, NF (WStepE c) M n :=
  normal_form_gen (fun _ _ h => wstep_wstepX (wstepE_wstep h)) (fun _ _ h => wstepE_compl h) hN
    hp hend

theorem normal_formX {c : ℝ} {L : ℕ → WLine} {N : ℕ} (hN : 1 ≤ N) (hp : Path (WStepX c) L N)
    (hend : L N = compl (L 0)) : ∃ M n, NF (WStepX c) M n :=
  normal_form_gen (fun _ _ h => h) (fun _ _ h => wstepX_compl h) hN hp hend

/-! ### The order on lines and replay -/

/-- Same quantifiers, every guess exponent and input constraint at most the other's. -/
def BLE : List Blk → List Blk → Prop
  | [], [] => True
  | u :: r, v :: s => u.q = v.q ∧ u.g ≤ v.g ∧ u.o ≤ v.o ∧ BLE r s
  | _, _ => False

/-- `LineLE B A`: B has the quantifier blocks and kernel type of A, and each of its exponents
(guess exponents, input constraints, kernel exponent) is at most the corresponding one of A. -/
def LineLE (B A : WLine) : Prop := BLE B.1 A.1 ∧ B.2.1 = A.2.1 ∧ B.2.2 ≤ A.2.2

theorem ble_refl : ∀ l : List Blk, BLE l l
  | [] => trivial
  | _ :: r => ⟨rfl, le_rfl, le_rfl, ble_refl r⟩

theorem lineLE_refl (L : WLine) : LineLE L L := ⟨ble_refl _, rfl, le_rfl⟩

theorem ble_nil : ∀ {r : List Blk}, BLE r [] → r = []
  | [], _ => rfl

theorem ble_pin : ∀ {r s : List Blk}, BLE r s → pin r ≤ pin s
  | [], [], _ => le_rfl
  | _ :: _, _ :: _, h => h.2.2.1

theorem ble_q : ∀ {r s : List Blk}, BLE r s → r.map Blk.q = s.map Blk.q
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [h.1, ble_q h.2.2.2]

theorem ble_outer {r s : List Blk} (h : BLE r s) : outer r = outer s := by
  have e : ∀ l : List Blk, outer l = (l.map Blk.q).getLast? := fun l => by
    simp [outer, List.getLast?_map]
  rw [e, e, ble_q h]

theorem ble_map : ∀ {r s : List Blk}, BLE r s → BLE (r.map cblk) (s.map cblk)
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨by simp [cblk, h.1], h.2.1, h.2.2.1, ble_map h.2.2.2⟩

theorem ble_append : ∀ {r₁ s₁ r₂ s₂ : List Blk}, BLE r₁ s₁ → BLE r₂ s₂ → BLE (r₁ ++ r₂) (s₁ ++ s₂)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h₁, h₂ => ⟨h₁.1, h₁.2.1, h₁.2.2.1, ble_append h₁.2.2.2 h₂⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem ble_split : ∀ {r : List Blk} (s₁ s₂ : List Blk), BLE r (s₁ ++ s₂) →
    ∃ r₁ r₂, r = r₁ ++ r₂ ∧ BLE r₁ s₁ ∧ BLE r₂ s₂
  | r, [], _, h => ⟨[], r, rfl, trivial, h⟩
  | [], _ :: _, _, h => h.elim
  | u :: _, _ :: s₁, s₂, h =>
    let ⟨r₁, r₂, e, h₁, h₂⟩ := ble_split s₁ s₂ h.2.2.2
    ⟨u :: r₁, r₂, by rw [e]; rfl, ⟨h.1, h.2.1, h.2.2.1, h₁⟩, h₂⟩

theorem lineLE_compl {B A : WLine} (h : LineLE B A) : LineLE (compl B) (compl A) :=
  ⟨ble_map h.1, by simp [compl, h.2.1], h.2.2⟩

/-- **Replay.** A `WStepX` step from A can be replayed from any line B ≤ A, landing at or below
the original target. -/
theorem replay {c : ℝ} (hc : 0 ≤ c) {A A' B : WLine} (h : WStepX c A A') (hB : LineLE B A) :
    ∃ B', WStepX c B B' ∧ LineLE B' A' := by
  obtain ⟨bm, km, am⟩ := B
  obtain ⟨hb, hk, ha⟩ := hB
  simp only at hb hk ha
  subst hk
  cases h with
  | speed bl k a x g g₂ o₁ o₂ a₂ hx hg hg₂ h₁ h₂ h₃ =>
    exact ⟨_, WStepX.speed bm _ am x g g₂ o₁ o₂ a₂ hx hg hg₂
      (le_trans (max_le_max (ble_pin hb) le_rfl) h₁) (le_trans (ble_pin hb) h₂) (by linarith),
      ⟨⟨rfl, le_rfl, le_rfl, rfl, le_rfl, le_rfl, hb⟩, rfl, le_rfl⟩⟩
  | speedMerge u rest k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃ =>
    obtain ⟨u', rest', rfl⟩ : ∃ u' rest', bm = u' :: rest' := by
      cases bm with
      | nil => exact hb.elim
      | cons u' rest' => exact ⟨u', rest', rfl⟩
    obtain ⟨hq', hg', ho', hr⟩ := hb
    exact ⟨_, WStepX.speedMerge u' rest' _ am x g g₂ o₁ o₂ a₂ (hq'.trans hq) hx
      (le_trans (max_le_max hg' le_rfl) hg) hg₂ (le_trans (max_le_max ho' le_rfl) h₁)
      (le_trans ho' h₂) (by linarith),
      ⟨⟨rfl, le_rfl, le_rfl, rfl, le_rfl, le_rfl, hr⟩, rfl, le_rfl⟩⟩
  | pop u rest k a e hq hcost =>
    obtain ⟨u', rest', rfl⟩ : ∃ u' rest', bm = u' :: rest' := by
      cases bm with
      | nil => exact hb.elim
      | cons u' rest' => exact ⟨u', rest', rfl⟩
    obtain ⟨hq', hg', ho', hr⟩ := hb
    refine ⟨_, WStepX.pop u' rest' _ am e (hq'.trans hq) (le_trans ?_ hcost), ⟨hr, rfl, le_rfl⟩⟩
    exact mul_le_mul_of_nonneg_left (max_le_max (max_le_max hg' ha) (max_le_max ho' (ble_pin hr)))
      hc
  | flip u rest k a e hcost =>
    obtain ⟨u', rest', rfl⟩ : ∃ u' rest', bm = u' :: rest' := by
      cases bm with
      | nil => exact hb.elim
      | cons u' rest' => exact ⟨u', rest', rfl⟩
    refine ⟨_, WStepX.flip u' rest' _ am e (le_trans ?_ hcost), ⟨hb, rfl, le_rfl⟩⟩
    exact mul_le_mul_of_nonneg_left (max_le_max ha hb.2.2.1) hc
  | flipQ k a e h =>
    obtain rfl := ble_nil hb
    exact ⟨_, WStepX.flipQ _ am e (le_trans (mul_le_mul_of_nonneg_left (max_le_max ha le_rfl) hc) h),
      ⟨trivial, rfl, le_rfl⟩⟩
  | combine bl bl' pre post u₁ u₂ w k a a' hbl hbl' h₁ hw hg ho hak =>
    subst hbl hbl'
    obtain ⟨r₁, r₂, rfl, hr₁, hr₂⟩ := ble_split pre _ hb
    cases r₂ with
    | nil => exact hr₂.elim
    | cons x r₂ =>
      cases r₂ with
      | nil => exact hr₂.2.2.2.elim
      | cons y post' =>
        obtain ⟨hq2, hg2, ho2, hr⟩ := hr₂
        obtain ⟨hq1, hg1, -, hpost⟩ := hr
        exact ⟨_, WStepX.combine _ _ r₁ post' y x w _ am am rfl rfl (by rw [hq1, hq2]; exact h₁)
          (by rw [hq2]; exact hw) (le_trans (max_le_max hg1 hg2) hg) (le_trans ho2 ho) le_rfl,
          ⟨ble_append hr₁ ⟨rfl, le_rfl, le_rfl, hpost⟩, rfl, le_trans ha hak⟩⟩
  | split bl bl' pre post w u₁ u₂ k a a' hbl hbl' h₁ h₂ ho hak =>
    subst hbl hbl'
    obtain ⟨r₁, r₂, rfl, hr₁, hr₂⟩ := ble_split pre _ hb
    cases r₂ with
    | nil => exact hr₂.elim
    | cons w' post' =>
      obtain ⟨hqw, -, how, hpost⟩ := hr₂
      exact ⟨_, WStepX.split _ _ r₁ post' w' u₁ u₂ _ am am rfl rfl (h₁.trans hqw.symm)
        (h₂.trans hqw.symm) (le_trans how ho) le_rfl,
        ⟨ble_append hr₁ ⟨rfl, le_rfl, le_rfl, rfl, le_rfl, le_rfl, hpost⟩, rfl, le_trans ha hak⟩⟩

theorem replay_path {c : ℝ} (hc : 0 ≤ c) {A : ℕ → WLine} :
    ∀ {n : ℕ}, Path (WStepX c) A n → ∀ {B₀ : WLine}, LineLE B₀ (A 0) →
      ∃ B : ℕ → WLine, B 0 = B₀ ∧ Path (WStepX c) B n ∧ ∀ j ≤ n, LineLE (B j) (A j)
  | 0, _, B₀, hB => ⟨fun _ => B₀, rfl, fun i hi => absurd hi (by omega), fun j hj => by
      obtain rfl : j = 0 := by omega
      exact hB⟩
  | n + 1, hp, B₀, hB => by
    obtain ⟨B, h0, hpB, hle⟩ := replay_path hc (n := n) (fun i hi => hp i (by omega)) hB
    obtain ⟨X, hX, hXle⟩ := replay hc (hp n (by omega)) (hle n (le_refl n))
    classical
    refine ⟨fun j => if j ≤ n then B j else X, by simp [h0], ?_, ?_⟩
    · intro i hi
      by_cases h : i + 1 ≤ n
      · simp only [show i ≤ n by omega, h, if_true]; exact hpB i (by omega)
      · obtain rfl : i = n := by omega
        simp only [le_refl, if_true, show ¬ i + 1 ≤ i by omega, if_false]; exact hX
    · intro j hj
      by_cases h : j ≤ n
      · simp only [h, if_true]; exact hle j h
      · obtain rfl : j = n + 1 := by omega
        simp only [h, if_false]; exact hXle

/-- The splice with an end line below the complement: from a quantifier-free line L i of a path
A ⇝ B with B ≤ ¬A there is a path of the same length to a line below ¬(L i). -/
theorem splice_le {c : ℝ} (hc : 0 ≤ c) {L : ℕ → WLine} {N : ℕ} (hp : Path (WStepX c) L N)
    (hend : LineLE (L N) (compl (L 0))) {i : ℕ} (hi : i ≤ N) :
    ∃ S : ℕ → WLine, Path (WStepX c) S N ∧ S 0 = L i ∧ LineLE (S N) (compl (L i)) := by
  obtain ⟨B, hB0, hpB, hBle⟩ := replay_path hc (A := fun j => compl (L j)) (n := i)
    (fun j hj => wstepX_compl (hp j (by omega))) hend
  classical
  refine ⟨fun t => if t ≤ N - i then L (i + t) else B (t - (N - i)), ?_, by simp, ?_⟩
  · intro t ht
    by_cases h1 : t + 1 ≤ N - i
    · simp only [show t ≤ N - i by omega, h1, if_true]
      rw [show i + (t + 1) = i + t + 1 by omega]; exact hp _ (by omega)
    · by_cases h2 : t ≤ N - i
      · obtain rfl : t = N - i := by omega
        simp only [le_refl, if_true, h1, if_false]
        rw [show i + (N - i) = N by omega, show N - i + 1 - (N - i) = 0 + 1 by omega, ← hB0]
        exact hpB 0 (by omega)
      · simp only [h2, h1, if_false]
        rw [show t + 1 - (N - i) = t - (N - i) + 1 by omega]
        exact hpB _ (by omega)
  · by_cases h : N ≤ N - i
    · obtain rfl : i = 0 := by omega
      simp only [h, if_true, Nat.zero_add]; exact hend
    · simp only [h, if_false]
      rw [show N - (N - i) = i by omega]
      exact hBle i le_rfl

/-! ### Impossibility for c³ ≥ 4 -/

theorem pos_of_cube {c : ℝ} (hc3 : 4 ≤ c ^ 3) : 0 < c := by
  by_contra h
  push Not at h
  have : c ^ 3 ≤ 0 := by
    have hsq : 0 ≤ c ^ 2 := sq_nonneg c
    have : c ^ 3 = c * c ^ 2 := by ring
    rw [this]; exact mul_nonpos_of_nonpos_of_nonneg h hsq
  linarith

theorem one_lt_of_cube {c : ℝ} (hc3 : 4 ≤ c ^ 3) : 1 < c := by
  have h0 := pos_of_cube hc3
  by_contra h
  push Not at h
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg h0.le h0.le), mul_le_mul_of_nonneg_left h h0.le]

/-- **No normal-form proof in the extended calculus** (W13 Definition 6.4), for c³ ≥ 4. -/
theorem no_nfX {c : ℝ} (hc3 : 4 ≤ c ^ 3) (M : ℕ → WLine) (n : ℕ) : ¬ NF (WStepX c) M n := by
  rintro ⟨hn, hpM, h0, -, hNM, -, hmid, hle⟩
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    have he := (step_nil_nil (hpM 0 (by omega)) h0 hNM).2
    have hc1 := one_lt_of_cube hc3
    have hm : 0 < max (M 0).2.2 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    nlinarith [le_max_left (M 0).2.2 1, mul_pos (sub_pos.mpr hc1) hm]
  · obtain ⟨T, hT⟩ := nf_trefutes (pos_of_cube hc3) h2 hpM h0 hNM hmid hle
    exact no_trefutation hc3 _ T hT

/-- **Main theorem (extended calculus).** For c³ ≥ 4 there is no `WStepX` path of length N ≥ 1
from any line A to a line B ≤ ¬A; in particular none to ¬A itself. -/
theorem no_proofX {c : ℝ} (hc3 : 4 ≤ c ^ 3) (L : ℕ → WLine) (N : ℕ) (hN : 1 ≤ N)
    (hp : Path (WStepX c) L N) : ¬ LineLE (L N) (compl (L 0)) := by
  intro hend
  have hstrict := qf_strict (c := c) (R := WStepX c) (fun _ _ h => h)
    (fun _ _ h => wstepX_compl h) (fun ⟨M, n, h⟩ => no_nfX hc3 M n h)
  obtain ⟨i, hi, hqf⟩ := exists_qf (fun _ _ h => h) hp (ble_outer hend.1)
  obtain ⟨S, hS, hS0, hSN⟩ := splice_le (pos_of_cube hc3).le hp hend hi
  have hSq : (S N).1 = [] := ble_nil (by simpa [compl, hqf] using hSN.1)
  have hlt := hstrict N S hN hS (by rw [hS0]; exact hqf) hSq
  rw [hS0] at hlt
  have hle := hSN.2.2
  simp only [compl] at hle
  linarith

/-- The same for the exact extended rules. -/
theorem no_proofXE {c : ℝ} (hc3 : 4 ≤ c ^ 3) (L : ℕ → WLine) (N : ℕ) (hN : 1 ≤ N)
    (hp : Path (WStepXE c) L N) : ¬ LineLE (L N) (compl (L 0)) :=
  no_proofX hc3 L N hN (fun i hi => wstepXE_wstepX (hp i hi))

/-- **No proof A ⊆ ¬A in the merging calculus (LP form)**, a corollary of `no_proofX`. -/
theorem no_literal_proof {c : ℝ} (hc3 : 4 ≤ c ^ 3) (L : ℕ → WLine) (N : ℕ) (hN : 1 ≤ N)
    (hp : Path (WStep c) L N) : L N ≠ compl (L 0) := fun hend =>
  no_proofX hc3 L N hN (fun i hi => wstep_wstepX (hp i hi)) (hend ▸ lineLE_refl _)

/-- The same for the exact rules of Lemmas 6.1/6.2. -/
theorem no_literal_proofE {c : ℝ} (hc3 : 4 ≤ c ^ 3) (L : ℕ → WLine) (N : ℕ) (hN : 1 ≤ N)
    (hp : Path (WStepE c) L N) : L N ≠ compl (L 0) :=
  no_literal_proof hc3 L N hN (fun i hi => wstepE_wstep (hp i hi))

/-- Normal-form proofs (Definition 6.4) in the merging calculus do not exist either, for c³ ≥ 4. -/
theorem no_nf {c : ℝ} (hc3 : 4 ≤ c ^ 3) (M : ℕ → WLine) (n : ℕ) : ¬ NF (WStep c) M n := fun h =>
  no_nfX hc3 M n ⟨h.1, fun i hi => wstep_wstepX (h.2.1 i hi), h.2.2⟩

/-! ### Non-vacuity in the literal format -/

/-- W13's §6 example NTS[n²] ⊆ (∃n)¹(∀ log n)¹NTS[n] ⊆ … ⊆ coNTS[n^{c³}], exact rules, c = 5/4. -/
noncomputable def w5 : ℕ → WLine
  | 0 => ([], true, 2)
  | 1 => ([⟨false, 0, 1⟩, ⟨true, 1, 1⟩], true, 1)
  | 2 => ([⟨false, 0, 1⟩, ⟨true, 1, 1⟩], false, 5 / 4)
  | 3 => ([⟨true, 1, 1⟩], true, 25 / 16)
  | _ => ([], false, 125 / 64)

theorem w5_nf : NF (WStepE (5 / 4)) w5 4 := by
  refine ⟨by norm_num, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i hi
    match i, hi with
    | 0, _ =>
      show WStepE (5 / 4) (w5 0) (w5 1)
      have := WStepE.speedNew (c := 5 / 4) [] true 2 1 (by simp) (by simp [pin]) (by norm_num)
        (by norm_num)
      simp only [w5]
      convert this using 2 <;> norm_num [pin]
    | 1, _ =>
      show WStepE (5 / 4) (w5 1) (w5 2)
      have := WStepE.flip (c := 5 / 4) ⟨false, 0, 1⟩ [⟨true, 1, 1⟩] true 1 (by simp)
      simp only [w5]
      convert this using 2; norm_num
    | 2, _ =>
      show WStepE (5 / 4) (w5 2) (w5 3)
      have := WStepE.pop (c := 5 / 4) ⟨false, 0, 1⟩ [⟨true, 1, 1⟩] false (5 / 4) rfl
      simp only [w5]
      convert this using 2; norm_num [pin]
    | 3, _ =>
      show WStepE (5 / 4) (w5 3) (w5 4)
      have := WStepE.pop (c := 5 / 4) ⟨true, 1, 1⟩ [] true (25 / 16) rfl
      simp only [w5]
      convert this using 2; norm_num [pin]
  · intro i h1 h2
    match i, h1, h2 with
    | 1, _, _ => simp [w5]
    | 2, _, _ => simp [w5]
    | 3, _, _ => simp [w5]
  · simp only [w5]; norm_num

/-- A literal proof A ⊆ ¬A with exact rules: NTS[n^{25/9}] ⊆ … ⊆ coNTS[n^{25/9}] at c = 5/4. -/
noncomputable def wq : ℕ → WLine
  | 0 => ([], true, 25 / 9)
  | 1 => ([⟨false, 0, 1⟩, ⟨true, 16 / 9, 16 / 9⟩], true, 1)
  | 2 => ([⟨false, 0, 1⟩, ⟨true, 16 / 9, 16 / 9⟩], false, 5 / 4)
  | 3 => ([⟨true, 16 / 9, 16 / 9⟩], true, 20 / 9)
  | _ => ([], false, 25 / 9)

theorem wq_proof : Path (WStepE (5 / 4)) wq 4 ∧ wq 4 = compl (wq 0) := by
  refine ⟨?_, by simp [wq, compl]⟩
  intro i hi
  match i, hi with
  | 0, _ =>
    show WStepE (5 / 4) (wq 0) (wq 1)
    have := WStepE.speedNew (c := 5 / 4) [] true (25 / 9) (16 / 9) (by simp) (by simp [pin])
      (by norm_num) (by norm_num)
    simp only [wq]
    convert this using 2 <;> norm_num [pin]
  | 1, _ =>
    show WStepE (5 / 4) (wq 1) (wq 2)
    have := WStepE.flip (c := 5 / 4) ⟨false, 0, 1⟩ [⟨true, 16 / 9, 16 / 9⟩] true 1 (by simp)
    simp only [wq]
    convert this using 2; norm_num
  | 2, _ =>
    show WStepE (5 / 4) (wq 2) (wq 3)
    have := WStepE.pop (c := 5 / 4) ⟨false, 0, 1⟩ [⟨true, 16 / 9, 16 / 9⟩] false (5 / 4) rfl
    simp only [wq]
    convert this using 2; norm_num [pin]
  | 3, _ =>
    show WStepE (5 / 4) (wq 3) (wq 4)
    have := WStepE.pop (c := 5 / 4) ⟨true, 16 / 9, 16 / 9⟩ [] true (20 / 9) rfl
    simp only [wq]
    convert this using 2; norm_num [pin]

/-- The identity of W13 §2 as one exact step: (∃n)¹(∃n)¹ NTS[n] ⊆ (∃n)¹ NTS[n]. -/
theorem w13_combine (c : ℝ) :
    WStepXE c ([⟨true, 1, 1⟩, ⟨true, 1, 1⟩], true, 1) ([⟨true, 1, 1⟩], true, 1) := by
  have := WStepXE.combine (c := c) [] [] true true 1 1 1
  simpa using this

/-- The last step of the derivation on W13 p. A:27 (default input constraints max(·,1)):
(∃ n^{cy})(∀ log n)¹(∀ n^y) coNTS[n^{cy}] ⊆ (∃ n^{cy})(∀ n^{cy}) coNTS[n^{cy}], for c ≥ 1, y ≥ 0. -/
theorem a27_combine {c y : ℝ} (hc : 1 ≤ c) (hy : 0 ≤ y) :
    WStepX c ([⟨false, y, max y 1⟩, ⟨false, 0, 1⟩, ⟨true, c * y, max (c * y) 1⟩], false, c * y)
      ([⟨false, c * y, max (c * y) 1⟩, ⟨true, c * y, max (c * y) 1⟩], false, c * y) := by
  have hyc : y ≤ c * y := by nlinarith
  exact WStepX.combine _ _ [] [⟨true, c * y, max (c * y) 1⟩] ⟨false, 0, 1⟩ ⟨false, y, max y 1⟩
    ⟨false, c * y, max (c * y) 1⟩ false (c * y) (c * y) rfl rfl rfl rfl
    (max_le (by positivity) hyc) (max_le_max hyc le_rfl) le_rfl

/-- The same step with the omitted input constraints read positionally (W13 §2 indexing): the
constraint after the outer ∃ block is 1 before the step and x after it, and the inner ∀ block
carries x. For 1 ≤ y ≤ x it is three steps: split the ∃ block, recombine it, combine the ∀ blocks. -/
theorem a27_combine_indexed (c : ℝ) {y x : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) :
    ∃ I J : WLine,
      WStepX c ([⟨false, y, x⟩, ⟨false, 0, 1⟩, ⟨true, x, 1⟩], false, x) I ∧ WStepX c I J ∧
      WStepX c J ([⟨false, x, x⟩, ⟨true, x, x⟩], false, x) := by
  let p : List Blk := [⟨false, y, x⟩, ⟨false, 0, 1⟩]
  let u : Blk := ⟨true, x, 1⟩
  let w : Blk := ⟨true, x, x⟩
  refine ⟨(p ++ [u, u], false, x), (p ++ [w], false, x), ?_, ?_, ?_⟩
  · exact WStepX.split _ _ p [] u u u _ _ _ rfl rfl rfl rfl le_rfl le_rfl
  · exact WStepX.combine _ _ p [] u u w _ _ _ rfl rfl rfl rfl (by simp [u, w]) (hy.trans hxy) le_rfl
  · exact WStepX.combine _ _ [] [w] ⟨false, 0, 1⟩ ⟨false, y, x⟩ ⟨false, x, x⟩ _ _ _
      rfl rfl rfl rfl (max_le (by linarith) hxy) le_rfl le_rfl

end TW
end PastaMath.TautThreshold
