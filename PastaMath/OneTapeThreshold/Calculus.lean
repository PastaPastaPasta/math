-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

/-!
# Williams's alternation-trading calculus for d-dimensional one-tape machines

The calculus of R. Williams, "Alternation-trading proofs, linear programming, and lower bounds"
(ACM TOCT 5(2), 2013; numbering of the TOCT version), §7.1, for the hypothesis
NTIME[n] ⊆ DTIME_d[n^c], with the DTISP speedup Lemma 3.3 applied inside a prefix (§4, Speedup
Rules 1 and 2) and the class syntax of §2.

A line `(bl, k)` is `(Q₁ n^{g₁})^{o₁} ⋯ (Q_m n^{g_m})^{o_m} K`. The block list `bl` is stored
innermost first; a block `Blk` has a quantifier `q` (`true` is ∃), a guess exponent `g` (0 stands
for log n) and an output superscript `o` (Williams's b_{i+1}). The kernel is `Ker.T a`
(DTIME_d[n^a]) or `Ker.S a e` (DTISP[n^a, n^e]). `pin bl` is the input superscript of the kernel:
the `o` of the innermost block, or 1 when `bl = []`.

`Step c d` has one constructor per rule, with the exact outputs of the §2.4 reading:

* `convMerge u rest a s` (Lemma 7.1, new block merged into the innermost block, which has the same
  quantifier): from `(u :: rest, T a)` with 0 < s ≤ a and 1 ≤ u.o to
  `(⟨u.q, max u.g (a − s), max (a − s) u.o⟩ :: rest, S a (d·s))`;
* `convNew bl q a s` (Lemma 7.1, new block): if the innermost block of `bl` (if any) has quantifier
  ≠ q, 0 < s ≤ a and 1 ≤ pin bl, from `(bl, T a)` to
  `(⟨q, a − s, max (a − s) (pin bl)⟩ :: bl, S a (d·s))`;
* `speedMerge u rest a e x` (Lemma 3.3 in a prefix, Speedup Rule 1): if 1 ≤ a, 0 ≤ e ≤ a − x,
  0 ≤ x ≤ a − 1 and 1 ≤ u.o, from `(u :: rest, S a e)` to
  `(⟨¬u.q, 0, max u.o e⟩ :: ⟨u.q, max u.g (x + e), max u.o (x + e)⟩ :: rest, S (a − x) e)`;
* `speedNew bl q a e x` (Lemma 3.3, Speedup Rule 2, two new blocks): if the innermost block of `bl`
  (if any) has quantifier ≠ q, the same conditions on a, e, x hold and 1 ≤ pin bl, from `(bl, S a e)`
  to `(⟨¬q, 0, max (pin bl) e⟩ :: ⟨q, x + e, max (pin bl) (x + e)⟩ :: bl, S (a − x) e)`;
* `slow u rest k` (Lemma 7.2): if 1 ≤ pin rest, 1 ≤ u.o, 1 ≤ time k and 0 ≤ u.g, from
  `(u :: rest, k)` to `(rest, T (c·max (max (pin rest) u.o) (max u.g (time k))))`.

`NF c d M n` is the strict normal form: n ≥ 1, `M 0, …, M n` is a `Step` path,
`M 0 = ([], T a)`, `M n = ([], T a')` with 1 ≤ a' < a, no line strictly between them has an empty
block list, and every line alternates (`Alt`: adjacent blocks have different quantifiers).

`nfCheck` is an executable checker over ℚ that replays a list of rule tags (`runQ`) from
DTIME_d[n^{a₀}] and tests the normal-form conditions; `nfCheck_sound` turns acceptance into an
`NF` path over ℝ at the same c and d, and `nfCheck_spec` says that this path is the replayed list of
lines cast to ℝ, of length `ts.length`.
-/

namespace PastaMath.OneTapeThreshold
namespace HY

/-- A quantifier block (Q n^g)^o: `q = true` is ∃ and `q = false` is ∀, `g` is the guess exponent
(0 stands for log n) and `o` the output superscript. -/
structure Blk where
  q : Bool
  g : ℝ
  o : ℝ

/-- The kernel of a line: `T a` is DTIME_d[n^a], `S a e` is DTISP[n^a, n^e]. -/
inductive Ker
  | T (a : ℝ)
  | S (a e : ℝ)

/-- The time exponent of a kernel: `a` for both `T a` and `S a e`. -/
def Ker.time : Ker → ℝ
  | .T a => a
  | .S a _ => a

/-- A line: its block list, innermost block first, and its kernel. -/
abbrev Line := List Blk × Ker

/-- The input superscript of the kernel: the output superscript of the innermost block, or 1 for an
empty block list. -/
def pin : List Blk → ℝ
  | [] => 1
  | u :: _ => u.o

/-- Adjacent blocks have different quantifiers. -/
def Alt : List Blk → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => u.q ≠ v.q ∧ Alt (v :: rest)

/-- One rule application at exponent c and dimension d. The constructors and their side
conditions are listed in the module docstring: `convMerge`, `convNew` (Lemma 7.1), `speedMerge`,
`speedNew` (Lemma 3.3 in a prefix, Speedup Rules 1 and 2) and `slow` (Lemma 7.2). -/
inductive Step (c d : ℝ) : Line → Line → Prop
  | convMerge (u : Blk) (rest : List Blk) (a s : ℝ) (hs : 0 < s) (hsa : s ≤ a) (hb : 1 ≤ u.o) :
      Step c d (u :: rest, .T a) (⟨u.q, max u.g (a - s), max (a - s) u.o⟩ :: rest, .S a (d * s))
  | convNew (bl : List Blk) (q : Bool) (a s : ℝ) (hq : ∀ u rest, bl = u :: rest → u.q ≠ q)
      (hs : 0 < s) (hsa : s ≤ a) (hb : 1 ≤ pin bl) :
      Step c d (bl, .T a) (⟨q, a - s, max (a - s) (pin bl)⟩ :: bl, .S a (d * s))
  | speedMerge (u : Blk) (rest : List Blk) (a e x : ℝ) (ha : 1 ≤ a) (he : 0 ≤ e)
      (hex : e ≤ a - x) (hx : 0 ≤ x) (hx1 : x ≤ a - 1) (hb : 1 ≤ u.o) :
      Step c d (u :: rest, .S a e)
        (⟨!u.q, 0, max u.o e⟩ :: ⟨u.q, max u.g (x + e), max u.o (x + e)⟩ :: rest, .S (a - x) e)
  | speedNew (bl : List Blk) (q : Bool) (a e x : ℝ) (hq : ∀ u rest, bl = u :: rest → u.q ≠ q)
      (ha : 1 ≤ a) (he : 0 ≤ e) (hex : e ≤ a - x) (hx : 0 ≤ x) (hx1 : x ≤ a - 1)
      (hb : 1 ≤ pin bl) :
      Step c d (bl, .S a e)
        (⟨!q, 0, max (pin bl) e⟩ :: ⟨q, x + e, max (pin bl) (x + e)⟩ :: bl, .S (a - x) e)
  | slow (u : Blk) (rest : List Blk) (k : Ker) (h1 : 1 ≤ pin rest) (h2 : 1 ≤ u.o)
      (h3 : 1 ≤ k.time) (h4 : 0 ≤ u.g) :
      Step c d (u :: rest, k) (rest, .T (c * max (max (pin rest) u.o) (max u.g k.time)))

/-- `M 0, …, M n` is an `R`-path: `R (M i) (M (i + 1))` for every i < n. -/
def Path (R : Line → Line → Prop) (M : ℕ → Line) (n : ℕ) : Prop := ∀ i < n, R (M i) (M (i + 1))

/-- Strict normal form: n ≥ 1; `M 0, …, M n` is a `Step c d` path; `M 0 = ([], T a)` and
`M n = ([], T a')` for some a, a'; `(M i).1 ≠ []` for 0 < i < n; 1 ≤ a'; a' < a; and every `M i`,
i ≤ n, alternates. -/
def NF (c d : ℝ) (M : ℕ → Line) (n : ℕ) : Prop :=
  1 ≤ n ∧ Path (Step c d) M n ∧ (∃ a, M 0 = ([], .T a)) ∧ (∃ a', M n = ([], .T a')) ∧
    (∀ i, 0 < i → i < n → (M i).1 ≠ []) ∧ 1 ≤ (M n).2.time ∧ (M n).2.time < (M 0).2.time ∧
    ∀ i ≤ n, Alt (M i).1

/-- `Step` with the output superscript of the new log n block of Lemma 3.3 given by `ℓ`: it is
`ℓ u.o e` for `speedMerge` and `ℓ (pin bl) e` for `speedNew`; every other output is the one of
`Step`. `StepO max` is `Step` (`step_of_stepO_max`), and `StepO (fun _ _ => 1)` is the calculus in
which that block has output exactly 1; `StepO (fun o _ => max o 1)` gives it the input superscript and
`StepO (fun _ e => max 1 e)` the output max(1, e). -/
inductive StepO (ℓ : ℝ → ℝ → ℝ) (c d : ℝ) : Line → Line → Prop
  | convMerge (u : Blk) (rest : List Blk) (a s : ℝ) (hs : 0 < s) (hsa : s ≤ a) (hb : 1 ≤ u.o) :
      StepO ℓ c d (u :: rest, .T a) (⟨u.q, max u.g (a - s), max (a - s) u.o⟩ :: rest, .S a (d * s))
  | convNew (bl : List Blk) (q : Bool) (a s : ℝ) (hq : ∀ u rest, bl = u :: rest → u.q ≠ q)
      (hs : 0 < s) (hsa : s ≤ a) (hb : 1 ≤ pin bl) :
      StepO ℓ c d (bl, .T a) (⟨q, a - s, max (a - s) (pin bl)⟩ :: bl, .S a (d * s))
  | speedMerge (u : Blk) (rest : List Blk) (a e x : ℝ) (ha : 1 ≤ a) (he : 0 ≤ e)
      (hex : e ≤ a - x) (hx : 0 ≤ x) (hx1 : x ≤ a - 1) (hb : 1 ≤ u.o) :
      StepO ℓ c d (u :: rest, .S a e)
        (⟨!u.q, 0, ℓ u.o e⟩ :: ⟨u.q, max u.g (x + e), max u.o (x + e)⟩ :: rest, .S (a - x) e)
  | speedNew (bl : List Blk) (q : Bool) (a e x : ℝ) (hq : ∀ u rest, bl = u :: rest → u.q ≠ q)
      (ha : 1 ≤ a) (he : 0 ≤ e) (hex : e ≤ a - x) (hx : 0 ≤ x) (hx1 : x ≤ a - 1)
      (hb : 1 ≤ pin bl) :
      StepO ℓ c d (bl, .S a e)
        (⟨!q, 0, ℓ (pin bl) e⟩ :: ⟨q, x + e, max (pin bl) (x + e)⟩ :: bl, .S (a - x) e)
  | slow (u : Blk) (rest : List Blk) (k : Ker) (h1 : 1 ≤ pin rest) (h2 : 1 ≤ u.o)
      (h3 : 1 ≤ k.time) (h4 : 0 ≤ u.g) :
      StepO ℓ c d (u :: rest, k) (rest, .T (c * max (max (pin rest) u.o) (max u.g k.time)))

/-- `NF` for `StepO ℓ c d`. `NFO (fun _ _ => 1) c d M n` is a strict normal-form proof in the
calculus in which the new log n block of Lemma 3.3 has output exactly 1. -/
def NFO (ℓ : ℝ → ℝ → ℝ) (c d : ℝ) (M : ℕ → Line) (n : ℕ) : Prop :=
  1 ≤ n ∧ Path (StepO ℓ c d) M n ∧ (∃ a, M 0 = ([], .T a)) ∧ (∃ a', M n = ([], .T a')) ∧
    (∀ i, 0 < i → i < n → (M i).1 ≠ []) ∧ 1 ≤ (M n).2.time ∧ (M n).2.time < (M 0).2.time ∧
    ∀ i ≤ n, Alt (M i).1

/-- The log n output `ℓ` lies between 1 and max(o, e) whenever 1 ≤ o and 0 ≤ e. -/
def LogOK (ℓ : ℝ → ℝ → ℝ) : Prop := ∀ o e : ℝ, 1 ≤ o → 0 ≤ e → 1 ≤ ℓ o e ∧ ℓ o e ≤ max o e

theorem logOK_max : LogOK max := fun _ _ ho _ => ⟨le_trans ho (le_max_left _ _), le_rfl⟩

theorem logOK_one : LogOK (fun _ _ => 1) := fun _ _ ho _ => ⟨le_rfl, le_trans ho (le_max_left _ _)⟩

/-- The output max(o, 1) (that is, o, since o ≥ 1): the input superscript of the kernel, as displayed in
Case 1 of Williams's sketch of Theorem 7.9 (p. A:37). -/
theorem logOK_in : LogOK (fun o _ => max o 1) :=
  fun _ _ ho _ => ⟨le_max_right _ _, max_le (le_max_left _ _) (le_trans ho (le_max_left _ _))⟩

/-- The output max(1, e): the output that Lemma 3.3 states for a quantifier-free DTISP class. -/
theorem logOK_sp : LogOK (fun _ e => max 1 e) :=
  fun _ _ ho _ => ⟨le_max_left _ _, max_le (le_trans ho (le_max_left _ _)) (le_max_right _ _)⟩

/-- `StepO max` is `Step`. -/
theorem step_of_stepO_max {c d : ℝ} {L L' : Line} (h : StepO max c d L L') : Step c d L L' := by
  cases h with
  | convMerge u rest a s hs hsa hb => exact Step.convMerge u rest a s hs hsa hb
  | convNew bl q a s hq hs hsa hb => exact Step.convNew bl q a s hq hs hsa hb
  | speedMerge u rest a e x ha he hex hx hx1 hb => exact Step.speedMerge u rest a e x ha he hex hx hx1 hb
  | speedNew bl q a e x hq ha he hex hx hx1 hb => exact Step.speedNew bl q a e x hq ha he hex hx hx1 hb
  | slow u rest k h1 h2 h3 h4 => exact Step.slow u rest k h1 h2 h3 h4

/-- `NFO max` is `NF`. -/
theorem nf_of_nfO_max {c d : ℝ} {M : ℕ → Line} {n : ℕ} (h : NFO max c d M n) : NF c d M n :=
  ⟨h.1, fun i hi => step_of_stepO_max (h.2.1 i hi), h.2.2⟩

structure BlkQ where
  q : Bool
  g : ℚ
  o : ℚ
  deriving DecidableEq

inductive KerQ
  | T (a : ℚ)
  | S (a e : ℚ)
  deriving DecidableEq

def KerQ.time : KerQ → ℚ
  | .T a => a
  | .S a _ => a

abbrev LineQ := List BlkQ × KerQ

def pinQ : List BlkQ → ℚ
  | [] => 1
  | u :: _ => u.o

def altQ : List BlkQ → Bool
  | [] => true
  | [_] => true
  | u :: v :: rest => (u.q != v.q) && altQ (v :: rest)

def headOk (bl : List BlkQ) (q : Bool) : Bool :=
  match bl with
  | [] => true
  | u :: _ => u.q != q

/-- A rule tag for the checker: the rule and its rational parameter (s for Lemma 7.1, x for
Lemma 3.3, the new quantifier for the unmerged rules). -/
inductive Tag
  | convMerge (s : ℚ)
  | convNew (q : Bool) (s : ℚ)
  | speedMerge (x : ℚ)
  | speedNew (q : Bool) (x : ℚ)
  | slow

/-- One rule over ℚ: the output line if the side conditions of the corresponding `Step` constructor
hold, `none` otherwise. -/
def stepQ (c d : ℚ) : Tag → LineQ → Option LineQ
  | .convMerge s, (u :: rest, .T a) =>
      if decide (0 < s) && decide (s ≤ a) && decide (1 ≤ u.o) then
        some (⟨u.q, max u.g (a - s), max (a - s) u.o⟩ :: rest, .S a (d * s)) else none
  | .convNew q s, (bl, .T a) =>
      if headOk bl q && decide (0 < s) && decide (s ≤ a) && decide (1 ≤ pinQ bl) then
        some (⟨q, a - s, max (a - s) (pinQ bl)⟩ :: bl, .S a (d * s)) else none
  | .speedMerge x, (u :: rest, .S a e) =>
      if decide (1 ≤ a) && decide (0 ≤ e) && decide (e ≤ a - x) && decide (0 ≤ x) &&
          decide (x ≤ a - 1) && decide (1 ≤ u.o) then
        some (⟨!u.q, 0, max u.o e⟩ :: ⟨u.q, max u.g (x + e), max u.o (x + e)⟩ :: rest, .S (a - x) e)
      else none
  | .speedNew q x, (bl, .S a e) =>
      if headOk bl q && decide (1 ≤ a) && decide (0 ≤ e) && decide (e ≤ a - x) && decide (0 ≤ x) &&
          decide (x ≤ a - 1) && decide (1 ≤ pinQ bl) then
        some (⟨!q, 0, max (pinQ bl) e⟩ :: ⟨q, x + e, max (pinQ bl) (x + e)⟩ :: bl, .S (a - x) e)
      else none
  | .slow, (u :: rest, k) =>
      if decide (1 ≤ pinQ rest) && decide (1 ≤ u.o) && decide (1 ≤ k.time) && decide (0 ≤ u.g) then
        some (rest, .T (c * max (max (pinQ rest) u.o) (max u.g k.time))) else none
  | _, _ => none

/-- Replays a tag list from a line; `none` if some step fails. -/
def runQ (c d : ℚ) : LineQ → List Tag → Option (List LineQ)
  | L, [] => some [L]
  | L, t :: ts =>
      match stepQ c d t L with
      | none => none
      | some M => (runQ c d M ts).map (L :: ·)

def isQF (L : LineQ) : Bool := L.1.isEmpty

def lastT (L : LineQ) : Option ℚ :=
  match L with
  | ([], .T a) => some a
  | _ => none

/-- Accepts when the tags replay from `([], T a0)`, there is at least one tag, the last line is
`([], T a')` with 1 ≤ a' < a0, no line strictly between the first and the last has an empty block list,
and every line alternates. -/
def nfCheck (c d a0 : ℚ) (ts : List Tag) : Bool :=
  match runQ c d ([], .T a0) ts with
  | none => false
  | some ls =>
      decide (1 ≤ ts.length) &&
      (match lastT (ls.getLastD ([], .T a0)) with
        | none => false
        | some a' => decide (1 ≤ a') && decide (a' < a0)) &&
      ((ls.drop 1).dropLast.all (fun L => !isQF L)) &&
      ls.all (fun L => altQ L.1)

def castB (u : BlkQ) : Blk := ⟨u.q, (u.g : ℝ), (u.o : ℝ)⟩

def castK : KerQ → Ker
  | .T a => .T (a : ℝ)
  | .S a e => .S (a : ℝ) (e : ℝ)

def castL (L : LineQ) : Line := (L.1.map castB, castK L.2)

theorem getD_lt {α : Type} {l : List α} {i : ℕ} {a : α} (h : i < l.length) :
    l.getD i a = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_ge {α : Type} {l : List α} {i : ℕ} {a : α} (h : l.length ≤ i) : l.getD i a = a := by
  simp [List.getD_eq_getElem?_getD, h]

theorem pin_cast (bl : List BlkQ) : pin (bl.map castB) = (pinQ bl : ℝ) := by
  cases bl <;> simp [pin, pinQ, castB]

theorem time_cast (k : KerQ) : (castK k).time = (k.time : ℝ) := by
  cases k <;> rfl

theorem headOk_sound {bl : List BlkQ} {q : Bool} (h : headOk bl q = true) :
    ∀ u rest, bl.map castB = u :: rest → u.q ≠ q := by
  intro u rest hb
  cases bl with
  | nil => simp at hb
  | cons v vs =>
    simp only [List.map_cons, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    simpa [headOk, castB] using h

theorem alt_cast (bl : List BlkQ) (h : altQ bl = true) : Alt (bl.map castB) := by
  induction bl with
  | nil => trivial
  | cons u rest ih =>
    cases rest with
    | nil => trivial
    | cons v vs =>
      simp only [altQ, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact ⟨by simpa [castB] using h.1, ih h.2⟩

/-- A successful rational step is a `Step` between the lines cast to ℝ. -/
theorem stepQ_sound {c d : ℚ} {t : Tag} {L M : LineQ} (h : stepQ c d t L = some M) :
    Step (c : ℝ) (d : ℝ) (castL L) (castL M) := by
  obtain ⟨bl, k⟩ := L
  cases t with
  | convMerge s =>
    cases bl with
    | nil => cases k <;> simp [stepQ] at h
    | cons u rest =>
      cases k with
      | S a e => simp [stepQ] at h
      | T a =>
        simp only [stepQ] at h
        split_ifs at h with hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨h1, h2⟩, h3⟩ := hc
        cases h
        have := Step.convMerge (c := (c : ℝ)) (d := (d : ℝ)) (castB u) (rest.map castB) (a : ℝ)
          (s : ℝ) (by exact_mod_cast h1) (by exact_mod_cast h2) (by simp only [castB]; exact_mod_cast h3)
        simpa [castL, castB, castK] using this
  | convNew q s =>
    cases k with
    | S a e => simp [stepQ] at h
    | T a =>
      simp only [stepQ] at h
      split_ifs at h with hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hc
      cases h
      have := Step.convNew (c := (c : ℝ)) (d := (d : ℝ)) (bl.map castB) q (a : ℝ) (s : ℝ)
        (headOk_sound h0) (by exact_mod_cast h1) (by exact_mod_cast h2)
        (by rw [pin_cast]; exact_mod_cast h3)
      simpa [castL, castB, castK, pin_cast] using this
  | speedMerge x =>
    cases bl with
    | nil => cases k <;> simp [stepQ] at h
    | cons u rest =>
      cases k with
      | T a => simp [stepQ] at h
      | S a e =>
        simp only [stepQ] at h
        split_ifs at h with hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
        cases h
        have := Step.speedMerge (c := (c : ℝ)) (d := (d : ℝ)) (castB u) (rest.map castB) (a : ℝ)
          (e : ℝ) (x : ℝ) (by exact_mod_cast h1) (by exact_mod_cast h2) (by exact_mod_cast h3)
          (by exact_mod_cast h4) (by exact_mod_cast h5) (by simp only [castB]; exact_mod_cast h6)
        simpa [castL, castB, castK] using this
  | speedNew q x =>
    cases k with
    | T a => simp [stepQ] at h
    | S a e =>
      simp only [stepQ] at h
      split_ifs at h with hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
      cases h
      have := Step.speedNew (c := (c : ℝ)) (d := (d : ℝ)) (bl.map castB) q (a : ℝ) (e : ℝ) (x : ℝ)
        (headOk_sound h0) (by exact_mod_cast h1) (by exact_mod_cast h2) (by exact_mod_cast h3)
        (by exact_mod_cast h4) (by exact_mod_cast h5) (by rw [pin_cast]; exact_mod_cast h6)
      simpa [castL, castB, castK, pin_cast] using this
  | slow =>
    cases bl with
    | nil => simp [stepQ] at h
    | cons u rest =>
      simp only [stepQ] at h
      split_ifs at h with hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      cases h
      simp only [castL, castK, List.map_cons, Rat.cast_mul, Rat.cast_max, ← pin_cast, ← time_cast]
      exact Step.slow (castB u) (rest.map castB) (castK k)
        (by rw [pin_cast]; exact_mod_cast h1) (by simp only [castB]; exact_mod_cast h2)
        (by rw [time_cast]; exact_mod_cast h3) (by simp only [castB]; exact_mod_cast h4)

/-- A successful replay of `ts` from `L` gives `ts.length + 1` lines starting with `L`, consecutive
lines (cast to ℝ) related by `Step`. -/
theorem runQ_spec {c d : ℚ} :
    ∀ (ts : List Tag) (L : LineQ) (ls : List LineQ), runQ c d L ts = some ls →
      ls.length = ts.length + 1 ∧ ls.head? = some L ∧
      ∀ i < ts.length, Step (c : ℝ) (d : ℝ) (castL (ls.getD i L)) (castL (ls.getD (i + 1) L))
  | [], L, ls, h => by
      simp only [runQ, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | t :: ts, L, ls, h => by
      simp only [runQ] at h
      split at h
      · simp at h
      · rename_i M hM
        cases hr : runQ c d M ts with
        | none => simp [hr] at h
        | some ls' =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hlen, hhead, hstep⟩ := runQ_spec ts M ls' hr
          refine ⟨by simp [hlen], rfl, ?_⟩
          intro i hi
          cases i with
          | zero =>
            cases ls' with
            | nil => simp at hlen
            | cons M' rest =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst hhead
              simpa using stepQ_sound hM
          | succ j =>
            have hj : j < ts.length := by simpa using hi
            have := hstep j hj
            have e1 : ∀ k, (L :: ls').getD (k + 1) L = ls'.getD k L := fun k => by simp
            rw [e1, e1]
            have e2 : ∀ k, k < ls'.length → ls'.getD k L = ls'.getD k M := by
              intro k hk; rw [getD_lt hk, getD_lt hk]
            rw [e2 j (by omega), e2 (j + 1) (by omega)]
            exact this

/-- If `nfCheck c d a0 ts = true` then the replay of `ts` from `([], T a0)` succeeds with some list
`ls` of lines, and these lines cast to ℝ form a strict normal-form proof `NF c d M n` with
n = `ts.length` (c and d cast to ℝ). -/
theorem nfCheck_spec {c d a0 : ℚ} {ts : List Tag} (h : nfCheck c d a0 ts = true) :
    ∃ ls, runQ c d ([], .T a0) ts = some ls ∧
      NF (c : ℝ) (d : ℝ) (fun i => castL (ls.getD i ([], .T a0))) ts.length := by
  unfold nfCheck at h
  cases hr : runQ c d ([], .T a0) ts with
  | none => simp [hr] at h
  | some ls =>
    rw [hr] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hn, hlast⟩, hmid⟩, halt⟩ := h
    obtain ⟨hlen, hhead, hstep⟩ := runQ_spec ts _ ls hr
    set L0 : LineQ := ([], .T a0) with hL0
    have h0 : ls.getD 0 L0 = L0 := by
      cases ls with
      | nil => simp at hlen
      | cons M rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        rw [← hhead]; rfl
    have hl : ls.getLastD L0 = ls.getD ts.length L0 := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
      simp [List.getD_eq_getElem?_getD, hlen]
    rw [hl] at hlast
    have hfin : ∃ a', ls.getD ts.length L0 = ([], .T a') ∧ 1 ≤ a' ∧ a' < a0 := by
      generalize ls.getD ts.length L0 = Lf at hlast ⊢
      obtain ⟨bl, k⟩ := Lf
      cases bl with
      | cons _ _ => simp [lastT] at hlast
      | nil =>
        cases k with
        | S _ _ => simp [lastT] at hlast
        | T a' =>
          simp only [lastT, Bool.and_eq_true, decide_eq_true_eq] at hlast
          exact ⟨a', rfl, hlast⟩
    obtain ⟨a', hfa, h1a, ha0⟩ := hfin
    refine ⟨ls, rfl, hn, fun i hi => hstep i hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨(a0 : ℝ), ?_⟩
      show castL (ls.getD 0 L0) = _
      rw [h0, hL0]; rfl
    · refine ⟨(a' : ℝ), ?_⟩
      show castL (ls.getD ts.length L0) = _
      rw [hfa]; rfl
    · intro i hi0 hi
      have hmem : ls.getD i L0 ∈ (ls.drop 1).dropLast := by
        rw [List.mem_iff_getElem]
        refine ⟨i - 1, by simp [hlen]; omega, ?_⟩
        simp only [List.getElem_dropLast, List.getElem_drop]
        rw [getD_lt (by omega)]
        congr 1; omega
      have := hmid _ hmem
      simp only [isQF] at this
      simpa [castL] using this
    · show (1 : ℝ) ≤ (castL (ls.getD ts.length L0)).2.time
      rw [hfa]; show (1 : ℝ) ≤ (a' : ℝ); exact_mod_cast h1a
    · show (castL (ls.getD ts.length L0)).2.time < (castL (ls.getD 0 L0)).2.time
      rw [hfa, h0, hL0]; show (a' : ℝ) < (a0 : ℝ); exact_mod_cast ha0
    · intro i _
      show Alt (castL (ls.getD i L0)).1
      by_cases hi : i < ls.length
      · have := halt _ (List.getElem_mem hi)
        rw [getD_lt hi]
        exact alt_cast _ this
      · rw [getD_ge (by omega), hL0]
        trivial

/-- If `nfCheck c d a0 ts = true` then there is a strict normal-form proof `NF c d M n` over ℝ (with
c and d cast to ℝ). -/
theorem nfCheck_sound {c d a0 : ℚ} {ts : List Tag} (h : nfCheck c d a0 ts = true) :
    ∃ M n, NF (c : ℝ) (d : ℝ) M n :=
  let ⟨_, _, hnf⟩ := nfCheck_spec h
  ⟨_, _, hnf⟩

end HY
end PastaMath.OneTapeThreshold
