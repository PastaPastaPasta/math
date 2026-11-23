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

That these rules coincide with W13's calculus is a modelling claim, not something Lean checks.

Main results: `sim`, `sim0` (every literal step is one or two `TStep`s, kernel clamped at 0);
`normal_form` (W13 Theorem 6.6 for this calculus: a proof A ⊆ ¬A yields a normal-form proof
NTS[n^a] ⊆ … ⊆ coNTS[n^{a'}], a' ≤ a); `nf_trefutes`; `literal_trefutes`; and
`no_literal_proof` / `no_literal_proofE`: for c³ ≥ 4 no rule sequence of length ≥ 1 leads from
any line A to its complement ¬A.
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

def Alt : List Blk → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => u.q ≠ v.q ∧ Alt (v :: rest)

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

theorem wstepE_wstep {c : ℝ} {L L' : WLine} (h : WStepE c L L') : WStep c L L' := by
  cases h with
  | speedNew bl k a x hq hb ha hx =>
    exact WStep.speedNew bl k a x x 0 _ _ _ hq hx le_rfl le_rfl le_rfl le_rfl le_rfl
  | speedMerge u rest k a x hq hb ha hx =>
    exact WStep.speedMerge u rest k a x _ 0 _ _ _ hq hx le_rfl le_rfl le_rfl le_rfl le_rfl
  | pop u rest k a hq => exact WStep.pop u rest k a _ hq le_rfl
  | flip u rest k a hq => exact WStep.flip u rest k a _ hq le_rfl

/-! ### Encoding into the reduced system -/

def mflag (bl : List Blk) (k : Bool) : Bool :=
  match bl with
  | [] => true
  | u :: _ => decide (u.q = k)

/-- Output superscripts outermost first, "kernel matches the innermost block", kernel clamped at 0. -/
noncomputable def enc (L : WLine) : TLine := ((L.1.map Blk.o).reverse, mflag L.1 L.2.1, max L.2.2 0)

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

theorem map_rev3 (rest : List Blk) (x y z : Blk) :
    ((x :: y :: z :: rest).map Blk.o).reverse = (rest.map Blk.o).reverse ++ [z.o, y.o, x.o] := by
  simp

theorem map_rev2 (rest : List Blk) (x y : Blk) :
    ((x :: y :: rest).map Blk.o).reverse = (rest.map Blk.o).reverse ++ [y.o, x.o] := by
  simp

theorem map_rev1 (rest : List Blk) (x : Blk) :
    ((x :: rest).map Blk.o).reverse = (rest.map Blk.o).reverse ++ [x.o] := by
  simp

/-- **Simulation lemma, nonempty prefix.** One literal step is one reduced step. -/
theorem sim {c : ℝ} (hc : 0 ≤ c) {L L' : WLine} (h : WStep c L L') (hne : L.1 ≠ [])
    (hA : Alt L.1) : TStep c (enc L) (enc L') := by
  cases h with
  | speedNew bl k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃ =>
    obtain ⟨u, rest, rfl⟩ : ∃ u rest, bl = u :: rest := by
      cases bl with
      | nil => exact absurd rfl hne
      | cons u rest => exact ⟨u, rest, rfl⟩
    have hq' := hq u rest rfl
    have e1 : enc (u :: rest, k, a) = ((rest.map Blk.o).reverse ++ [u.o], false, max a 0) := by
      simp only [enc, mflag, map_rev1]; simp [hq']
    have e2 : enc (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: u :: rest, k, a₂) =
        ((rest.map Blk.o).reverse ++ [u.o, o₁, o₂], false, max a₂ 0) := by
      simp only [enc, mflag, map_rev3]; simp
    rw [e1, e2]
    exact TStep.speedO _ u.o (max a 0) (min x (max a 0)) o₁ o₂ (max a₂ 0)
      (le_min hx (le_max_right _ _)) (min_le_right _ _)
      (le_trans (max_le_max (min_le_left _ _) le_rfl) (by rw [max_comm]; exact h₁)) h₂
      (clamp_sub hx h₃)
  | speedMerge u rest k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃ =>
    have e1 : enc (u :: rest, k, a) = ((rest.map Blk.o).reverse ++ [u.o], true, max a 0) := by
      simp only [enc, mflag, map_rev1]; simp [hq]
    have e2 : enc (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: rest, k, a₂) =
        ((rest.map Blk.o).reverse ++ [o₁, o₂], false, max a₂ 0) := by
      simp only [enc, mflag, map_rev2]; simp
    rw [e1, e2]
    exact TStep.speedM _ u.o (max a 0) (min x (max a 0)) o₁ o₂ (max a₂ 0)
      (le_min hx (le_max_right _ _)) (min_le_right _ _)
      (le_trans (max_le_max (min_le_left _ _) le_rfl) (by rw [max_comm]; exact h₁)) h₂
      (clamp_sub hx h₃)
  | pop u rest k a e hq hcost =>
    have e1 : enc (u :: rest, k, a) = ((rest.map Blk.o).reverse ++ [u.o], true, max a 0) := by
      simp only [enc, mflag, map_rev1]; simp [hq]
    cases rest with
    | nil =>
      have e2 : enc (([] : List Blk), !k, e) = ([], true, max e 0) := by simp [enc, mflag]
      rw [e1, e2]
      refine TStep.pop [] u.o (max a 0) (max e 0) ?_
      rw [top_nil]
      refine cmax_le hc ?_ hcost
      simp only [pin]
      apply le_trans _ (le_max_left _ _)
      refine max_le (le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_right _ _)))
        (max_le (le_trans (le_max_left _ _) (le_max_right _ _)) (max_le ?_ ?_))
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
      · exact le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_right _ _))
    | cons v rest' =>
      have hvq : v.q ≠ u.q := fun h' => hA.1 h'.symm
      have e2 : enc (v :: rest', !k, e) = ((rest'.map Blk.o).reverse ++ [v.o], true, max e 0) := by
        simp only [enc, mflag, map_rev1]
        have : v.q = !k := by
          rw [← hq]; cases hv : v.q <;> cases hu : u.q <;> simp_all
        simp [this]
      rw [e1, e2, map_rev1]
      refine TStep.pop _ u.o (max a 0) (max e 0) ?_
      rw [top_concat]
      refine cmax_le hc ?_ hcost
      simp only [pin]
      refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
      · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
      · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
      · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
      · exact le_max_right _ _
  | flip u rest k a e hq hcost =>
    have e1 : enc (u :: rest, k, a) = ((rest.map Blk.o).reverse ++ [u.o], false, max a 0) := by
      simp only [enc, mflag, map_rev1]; simp [hq]
    have e2 : enc (u :: rest, !k, e) = ((rest.map Blk.o).reverse ++ [u.o], !false, max e 0) := by
      simp only [enc, mflag, map_rev1]
      have : u.q = !k := by cases hu : u.q <;> cases k <;> simp_all
      simp [this]
    rw [e1, e2]
    refine TStep.flip _ u.o (max a 0) (max e 0) false ?_
    refine cmax_le hc ?_ hcost
    exact max_le (le_trans (le_max_right _ _) (le_max_left _ _))
      (max_le (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _))

/-- **Simulation lemma, empty prefix.** A literal step from a quantifier-free line is `init`
followed by this reduced step. -/
theorem sim0 {c : ℝ} {L L' : WLine} (h : WStep c L L') (he : L.1 = []) :
    TStep c ([0], true, max L.2.2 0) (enc L') := by
  obtain ⟨bl, k, a⟩ := L
  simp only at he
  subst he
  cases h with
  | speedNew bl k a x g g₂ o₁ o₂ a₂ hq hx hg hg₂ h₁ h₂ h₃ =>
    have e2 : enc (⟨!k, g₂, o₂⟩ :: ⟨k, g, o₁⟩ :: [], k, a₂) = ([] ++ [o₁, o₂], false, max a₂ 0) := by
      simp [enc, mflag]
    rw [e2]
    simp only [pin] at h₁ h₂
    exact TStep.speedM [] 0 (max a 0) (min x (max a 0)) o₁ o₂ (max a₂ 0)
      (le_min hx (le_max_right _ _)) (min_le_right _ _)
      (max_le (le_trans (min_le_left _ _) (le_trans (le_max_right _ _) h₁))
        (le_trans zero_le_one (le_trans (le_max_left _ _) h₁)))
      (le_trans zero_le_one h₂) (clamp_sub hx h₃)

theorem enc_nil {L : WLine} (he : L.1 = []) : enc L = ([], true, max L.2.2 0) := by
  obtain ⟨bl, k, a⟩ := L
  simp only at he
  subst he
  simp [enc, mflag]

theorem enc_ne {L : WLine} (hne : L.1 ≠ []) : (enc L).1 ≠ [] := by
  simp [enc, hne]

/-! ### Invariants of the literal calculus -/

theorem step_from_nil {c : ℝ} {L L' : WLine} (h : WStep c L L') (he : L.1 = []) : L'.1 ≠ [] := by
  cases h <;> simp_all

theorem pop_pos {c : ℝ} (hc : 0 ≤ c) {L L' : WLine} (h : WStep c L L') (he : L'.1 = []) :
    c ≤ L'.2.2 := by
  cases h with
  | speedNew => simp at he
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

theorem alt_tail {u : Blk} {rest : List Blk} (h : Alt (u :: rest)) : Alt rest := by
  cases rest with
  | nil => trivial
  | cons v r => exact h.2

theorem alt_step {c : ℝ} {L L' : WLine} (h : WStep c L L') (hA : Alt L.1) : Alt L'.1 := by
  cases h with
  | speedNew bl k a x g g₂ o₁ o₂ a₂ hq =>
    refine ⟨by simp, ?_⟩
    cases bl with
    | nil => trivial
    | cons u rest => exact ⟨fun h' => hq u rest rfl h'.symm, hA⟩
  | speedMerge u rest k a x g g₂ o₁ o₂ a₂ hq =>
    refine ⟨by simp, ?_⟩
    cases rest with
    | nil => trivial
    | cons v r => exact ⟨by rw [← hq]; exact hA.1, hA.2⟩
  | pop u rest k a e hq => exact alt_tail hA
  | flip => exact hA

def outer (bl : List Blk) : Option Bool := bl.getLast?.map Blk.q

theorem outer_cons2 (x y : Blk) (l : List Blk) : outer (x :: y :: l) = outer (y :: l) := by
  simp [outer, List.getLast?_cons_cons]

theorem outer_step {c : ℝ} {L L' : WLine} (h : WStep c L L') (hne : L.1 ≠ []) (hne' : L'.1 ≠ []) :
    outer L'.1 = outer L.1 := by
  cases h with
  | speedNew bl k a x g g₂ o₁ o₂ a₂ hq =>
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

theorem alt_map : ∀ bl : List Blk, Alt bl → Alt (bl.map cblk)
  | [], _ => trivial
  | [_], _ => trivial
  | u :: v :: rest, h => ⟨by simp [cblk]; exact h.1, alt_map (v :: rest) h.2⟩

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

/-! ### Paths, segments, normal form -/

def Path (R : WLine → WLine → Prop) (M : ℕ → WLine) (n : ℕ) : Prop := ∀ i < n, R (M i) (M (i + 1))

/-- W13 Definition 6.4 (normal form), in the calculus `R`: first line NTS[n^a], last line
coNTS[n^{a'}] with a' ≤ a, at least two lines, no other quantifier-free line; the first line is
a simple class. -/
def NF (R : WLine → WLine → Prop) (M : ℕ → WLine) (n : ℕ) : Prop :=
  1 ≤ n ∧ Path R M n ∧ (M 0).1 = [] ∧ (M 0).2.1 = true ∧ (M n).1 = [] ∧ (M n).2.1 = false ∧
    (∀ i, 0 < i → i < n → (M i).1 ≠ []) ∧ (M n).2.2 ≤ (M 0).2.2

theorem path_alt {c : ℝ} {M : ℕ → WLine} {n : ℕ} (hp : Path (WStep c) M n) (hA : Alt (M 0).1) :
    ∀ i ≤ n, Alt (M i).1 := by
  intro i
  induction i with
  | zero => intro _; exact hA
  | succ i ih => intro hi; exact alt_step (hp i (by omega)) (ih (by omega))

/-- Outer quantifier is constant along a stretch of quantified lines. -/
theorem stretch_outer {c : ℝ} (M : ℕ → WLine) (p : ℕ) :
    ∀ j, (∀ i, p ≤ i → i < p + j → WStep c (M i) (M (i + 1))) →
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
theorem seg_types {c : ℝ} {M : ℕ → WLine} {n : ℕ} (hn : 1 ≤ n) (hp : Path (WStep c) M n)
    (h0 : (M 0).1 = []) (hN : (M n).1 = []) (hmid : ∀ i, 0 < i → i < n → (M i).1 ≠ []) :
    (M n).2.1 = !(M 0).2.1 := by
  have hn2 : 2 ≤ n := by
    by_contra h'
    have : n = 1 := by omega
    subst this
    exact step_from_nil (hp 0 (by omega)) h0 hN
  have ho1 : outer (M 1).1 = some (M 0).2.1 := by
    have h01 := hp 0 (by omega)
    simp only [Nat.zero_add] at h01
    generalize M 0 = A at h01 h0 ⊢
    generalize M 1 = B at h01 ⊢
    obtain ⟨bl, k, a⟩ := A
    simp only at h0
    subst h0
    cases h01 with
    | speedNew bl k a x g g₂ o₁ o₂ a₂ => simp [outer]
  have hst := stretch_outer (c := c) M 1 (n - 2) (fun i h1 h2 => hp i (by omega))
    (fun i h1 h2 => hmid i (by omega) (by omega))
  rw [show 1 + (n - 2) = n - 1 by omega, ho1] at hst
  have hlast := hp (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at hlast
  generalize M (n - 1) = A at hst hlast
  generalize M n = B at hlast hN ⊢
  obtain ⟨bl, k, a⟩ := A
  obtain ⟨bl', k', a'⟩ := B
  simp only at hN hst ⊢
  subst hN
  cases hlast with
  | pop u rest k a e hq =>
    simp [outer] at hst
    rw [← hst, hq]

/-- W13 Lemma 6.5-level map: a normal-form literal proof (either orientation) gives a
`TRefutes` instance. -/
theorem nf_trefutes {c : ℝ} (hc : 0 < c) {M : ℕ → WLine} {n : ℕ} (hn : 1 ≤ n)
    (hp : Path (WStep c) M n) (h0 : (M 0).1 = []) (hN : (M n).1 = [])
    (hmid : ∀ i, 0 < i → i < n → (M i).1 ≠ []) (hle : (M n).2.2 ≤ (M 0).2.2) :
    ∃ T, TRefutes c (n + 1) T := by
  have hA : ∀ i ≤ n, Alt (M i).1 := path_alt hp (by rw [h0]; trivial)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by
    by_contra h'
    have : m = 0 := by omega
    subst this
    exact step_from_nil (hp 0 (by omega)) h0 hN
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
    | 1, _ => exact sim0 (hp 0 (by omega)) h0
    | j + 2, hj =>
      exact sim hc.le (hp (j + 1) (by omega)) (hmid _ (by omega) (by omega)) (hA _ (by omega))
  · intro i h1 h2
    match i, h1, h2 with
    | 1, _, _ => simp [T]
    | j + 2, _, hj => exact enc_ne (hmid _ (by omega) (by omega))

/-! Generic part: a calculus `R ⊆ WStep c` closed under complementation. -/
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
theorem exists_qf (hR : ∀ L L', R L L' → WStep c L L') {L : ℕ → WLine} {N : ℕ} (hp : Path R L N)
    (hend : L N = compl (L 0)) : ∃ i ≤ N, (L i).1 = [] := by
  by_contra hno
  push Not at hno
  have hst := stretch_outer (c := c) L 0 N (fun i _ h2 => hR _ _ (hp i (by omega)))
    (fun i _ h2 => hno i (by omega))
  simp only [Nat.zero_add] at hst
  rw [hend] at hst
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
theorem normal_form_gen (hR : ∀ L L', R L L' → WStep c L L')
    (hRc : ∀ L L', R L L' → R (compl L) (compl L')) {L : ℕ → WLine} {N : ℕ} (hN : 1 ≤ N)
    (hp : Path R L N) (hend : L N = compl (L 0)) : ∃ M n, NF R M n := by
  by_contra hno
  have hseg : ∀ (M : ℕ → WLine) (n : ℕ), 1 ≤ n → Path R M n → (M 0).1 = [] → (M n).1 = [] →
      (∀ i, 0 < i → i < n → (M i).1 ≠ []) → (M 0).2.2 < (M n).2.2 := by
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
  obtain ⟨i, hi, hqf⟩ := exists_qf hR hp hend
  obtain ⟨S, hS, hS0, hSN⟩ := splice hRc hp hend hi
  have := qf_up hseg N S hN hS (by rw [hS0]; exact hqf) (by rw [hSN]; simp [compl, hqf])
  rw [hS0, hSN] at this
  simp [compl] at this

end generic

theorem normal_form {c : ℝ} {L : ℕ → WLine} {N : ℕ} (hN : 1 ≤ N) (hp : Path (WStep c) L N)
    (hend : L N = compl (L 0)) : ∃ M n, NF (WStep c) M n :=
  normal_form_gen (fun _ _ h => h) (fun _ _ h => wstep_compl h) hN hp hend

theorem normal_formE {c : ℝ} {L : ℕ → WLine} {N : ℕ} (hN : 1 ≤ N) (hp : Path (WStepE c) L N)
    (hend : L N = compl (L 0)) : ∃ M n, NF (WStepE c) M n :=
  normal_form_gen (fun _ _ h => wstepE_wstep h) (fun _ _ h => wstepE_compl h) hN hp hend

/-- **Any literal proof yields a `TRefutes` instance** (for c > 0). -/
theorem literal_trefutes {c : ℝ} (hc : 0 < c) {L : ℕ → WLine} {N : ℕ} (hN : 1 ≤ N)
    (hp : Path (WStep c) L N) (hend : L N = compl (L 0)) : ∃ n T, TRefutes c n T := by
  obtain ⟨M, n, hn, hpM, h0, -, hNM, -, hmid, hle⟩ := normal_form hN hp hend
  obtain ⟨T, hT⟩ := nf_trefutes hc hn hpM h0 hNM hmid hle
  exact ⟨n + 1, T, hT⟩

theorem pos_of_cube {c : ℝ} (hc3 : 4 ≤ c ^ 3) : 0 < c := by
  by_contra h
  push Not at h
  have : c ^ 3 ≤ 0 := by
    have hsq : 0 ≤ c ^ 2 := sq_nonneg c
    have : c ^ 3 = c * c ^ 2 := by ring
    rw [this]; exact mul_nonpos_of_nonpos_of_nonneg h hsq
  linarith

/-- **No proof A ⊆ ¬A in the formalised calculus (LP form).** For c³ ≥ 4 there is no `WStep`
path of length N ≥ 1 from any line A to its complement ¬A. -/
theorem no_literal_proof {c : ℝ} (hc3 : 4 ≤ c ^ 3) (L : ℕ → WLine) (N : ℕ) (hN : 1 ≤ N)
    (hp : Path (WStep c) L N) : L N ≠ compl (L 0) := by
  intro hend
  obtain ⟨n, T, hT⟩ := literal_trefutes (pos_of_cube hc3) hN hp hend
  exact no_trefutation hc3 n T hT

/-- The same for the exact rules of Lemmas 6.1/6.2. -/
theorem no_literal_proofE {c : ℝ} (hc3 : 4 ≤ c ^ 3) (L : ℕ → WLine) (N : ℕ) (hN : 1 ≤ N)
    (hp : Path (WStepE c) L N) : L N ≠ compl (L 0) :=
  no_literal_proof hc3 L N hN (fun i hi => wstepE_wstep (hp i hi))

/-- Normal-form proofs (Definition 6.4) do not exist either, for c³ ≥ 4. -/
theorem no_nf {c : ℝ} (hc3 : 4 ≤ c ^ 3) (M : ℕ → WLine) (n : ℕ) : ¬ NF (WStep c) M n := by
  rintro ⟨hn, hpM, h0, -, hNM, -, hmid, hle⟩
  obtain ⟨T, hT⟩ := nf_trefutes (pos_of_cube hc3) hn hpM h0 hNM hmid hle
  exact no_trefutation hc3 _ T hT

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

end TW
end PastaMath.TautThreshold
