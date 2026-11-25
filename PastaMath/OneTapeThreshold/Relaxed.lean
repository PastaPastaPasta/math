-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The relaxed calculus and a one-level potential

`RStep c d` is a relaxation of `HY.Step` used for the impossibility results. A line keeps only the
output superscripts of its blocks (innermost first) and the kernel, `HK.T a` or `HK.S a e`;
quantifiers and guess exponents are dropped, the input superscript of the empty prefix is 0
(`pin [] = 0`), and every output is only bounded from below:

* `convM b rest a s b₁ a₂ e` (Lemma 7.1, merged): 0 ≤ s ≤ a, max b (a − s) ≤ b₁, a ≤ a₂, d·s ≤ e;
  from `(b :: rest, T a)` to `(b₁ :: rest, S a₂ e)`;
* `convN bl a s g a₂ e` (Lemma 7.1, new block): 0 ≤ s ≤ a, max (pin bl) (a − s) ≤ g, a ≤ a₂,
  d·s ≤ e; from `(bl, T a)` to `(g :: bl, S a₂ e)`;
* `speedM b rest a e x b' L a₂ e₂` (Lemma 3.3, merged): 0 ≤ x, e ≤ a − x, max b (x + e) ≤ b',
  max b e ≤ L, a − x ≤ a₂, e ≤ e₂; from `(b :: rest, S a e)` to `(L :: b' :: rest, S a₂ e₂)`;
* `speedN bl a e x g₁ g₂ a₂ e₂` (Lemma 3.3, two new blocks): 0 ≤ x, e ≤ a − x,
  max (pin bl) (x + e) ≤ g₁, max (pin bl) e ≤ g₂, a − x ≤ a₂, e ≤ e₂; from `(bl, S a e)` to
  `(g₂ :: g₁ :: bl, S a₂ e₂)`;
* `slow b rest k a'` (Lemma 7.2): c·max (max (pin rest) b) (time k) ≤ a'; from `(b :: rest, k)`
  to `(rest, T a')`.

`sim`: for c ≥ 0 every `HY.Step` is an `RStep` between the encodings `enc` (block outputs and
kernel).

The one-level potential: with g = 1/A, A = max(1 + 1/d, c), on a level with top superscript b,
ψ_T(b, a) = min(max(b, a), c·max(b, g·a)) and ψ_S(b, a, e) = min(max(b, a), c·max(b, e)), lifted
through the outer blocks by y ↦ ψ_T(b', c·max(b', y)) and finally y ↦ c·max(0, y) (`Phi`).
Under `Facts c d g` (1 ≤ c, 0 ≤ g, c·g ≤ 1, 1 ≤ c²·g, 0 ≤ d, g ≤ d·(1 − g)) the potential does not
decrease along `RStep` from lines with nonnegative entries (`phi_step`), so every quantifier-free
line `T a'` reached from `T a₀` (a₀ ≥ 0) has a' ≥ a₀ (`qf_ge`). `no_nf`: for d > 0, c ≥ 1 and
c² ≥ 1 + 1/d there is no `HY.NF` proof.
-/

namespace PastaMath.OneTapeThreshold
namespace HL

/-- The kernel of a relaxed line: `T a` (DTIME_d[n^a]) or `S a e` (DTISP[n^a, n^e]). -/
inductive HK
  | T (a : ℝ)
  | S (a e : ℝ)

def HK.time : HK → ℝ
  | .T a => a
  | .S a _ => a

/-- A relaxed line: the output superscripts of its blocks, innermost first, and its kernel. -/
abbrev RLine := List ℝ × HK

/-- The input superscript of the kernel in the relaxed calculus: the innermost superscript, or 0 for an
empty prefix. -/
def pin : List ℝ → ℝ
  | [] => 0
  | b :: _ => b

/-- The relaxed calculus; the constructors and their conditions are listed in the module
docstring. -/
inductive RStep (c d : ℝ) : RLine → RLine → Prop
  | convM (b : ℝ) (rest : List ℝ) (a s b₁ a₂ e : ℝ) (hs : 0 ≤ s) (hsa : s ≤ a)
      (h₁ : max b (a - s) ≤ b₁) (ha : a ≤ a₂) (he : d * s ≤ e) :
      RStep c d (b :: rest, .T a) (b₁ :: rest, .S a₂ e)
  | convN (bl : List ℝ) (a s g a₂ e : ℝ) (hs : 0 ≤ s) (hsa : s ≤ a)
      (hg : max (pin bl) (a - s) ≤ g) (ha : a ≤ a₂) (he : d * s ≤ e) :
      RStep c d (bl, .T a) (g :: bl, .S a₂ e)
  | speedM (b : ℝ) (rest : List ℝ) (a e x b' L a₂ e₂ : ℝ) (hx : 0 ≤ x) (hex : e ≤ a - x)
      (h' : max b (x + e) ≤ b') (hL : max b e ≤ L) (ha : a - x ≤ a₂) (he : e ≤ e₂) :
      RStep c d (b :: rest, .S a e) (L :: b' :: rest, .S a₂ e₂)
  | speedN (bl : List ℝ) (a e x g₁ g₂ a₂ e₂ : ℝ) (hx : 0 ≤ x) (hex : e ≤ a - x)
      (h₁ : max (pin bl) (x + e) ≤ g₁) (h₂ : max (pin bl) e ≤ g₂) (ha : a - x ≤ a₂) (he : e ≤ e₂) :
      RStep c d (bl, .S a e) (g₂ :: g₁ :: bl, .S a₂ e₂)
  | slow (b : ℝ) (rest : List ℝ) (k : HK) (a' : ℝ) (h : c * max (max (pin rest) b) k.time ≤ a') :
      RStep c d (b :: rest, k) (rest, .T a')

/-- `M 0, …, M n` is an `RStep c d` path. -/
def RPath (c d : ℝ) (M : ℕ → RLine) (n : ℕ) : Prop := ∀ i < n, RStep c d (M i) (M (i + 1))

def KNN : HK → Prop
  | .T a => 0 ≤ a
  | .S a e => 0 ≤ a ∧ 0 ≤ e

/-- Every superscript and every kernel exponent of the line is ≥ 0. -/
def NN (L : RLine) : Prop := (∀ b ∈ L.1, 0 ≤ b) ∧ KNN L.2

/-- The hypotheses of the one-level potential: 1 ≤ c, 0 ≤ g, c·g ≤ 1, 1 ≤ c²·g, 0 ≤ d and
g ≤ d·(1 − g). -/
structure Facts (c d g : ℝ) : Prop where
  c1 : 1 ≤ c
  g0 : 0 ≤ g
  cg : c * g ≤ 1
  c2g : 1 ≤ c ^ 2 * g
  d0 : 0 ≤ d
  dg : g ≤ d * (1 - g)

/-- ψ_T(b, a) = min(max(b, a), c·max(b, g·a)). -/
def psT (c g b a : ℝ) : ℝ := min (max b a) (c * max b (g * a))

/-- ψ_S(b, a, e) = min(max(b, a), c·max(b, e)). -/
def psS (c b a e : ℝ) : ℝ := min (max b a) (c * max b e)

def pot (c g b : ℝ) : HK → ℝ
  | .T a => psT c g b a
  | .S a e => psS c b a e

/-- Lifts a level value y through the outer superscripts: y ↦ ψ_T(b', c·max(b', y)) for each outer b',
then y ↦ c·max(0, y). -/
def up (c g : ℝ) : List ℝ → ℝ → ℝ
  | [], y => c * max 0 y
  | b :: rest, y => up c g rest (psT c g b (c * max b y))

/-- The potential of a line: `a` for `([], T a)`, 0 for `([], S a e)`, and the lifted value of the
innermost level otherwise. -/
def Phi (c g : ℝ) : RLine → ℝ
  | ([], .T a) => a
  | ([], .S _ _) => 0
  | (b :: rest, k) => up c g rest (pot c g b k)

section lemmas

variable {c d g : ℝ}

theorem psT_mono (F : Facts c d g) {b b' a a' : ℝ} (hb : b ≤ b') (ha : a ≤ a') :
    psT c g b a ≤ psT c g b' a' :=
  min_le_min (max_le_max hb ha)
    (mul_le_mul_of_nonneg_left (max_le_max hb (mul_le_mul_of_nonneg_left ha F.g0))
      (by linarith [F.c1]))

theorem psS_mono (F : Facts c d g) {b b' a a' e e' : ℝ} (hb : b ≤ b') (ha : a ≤ a') (he : e ≤ e') :
    psS c b a e ≤ psS c b' a' e' :=
  min_le_min (max_le_max hb ha) (mul_le_mul_of_nonneg_left (max_le_max hb he) (by linarith [F.c1]))

theorem psT_ge (F : Facts c d g) {b a : ℝ} (hb : 0 ≤ b) : b ≤ psT c g b a := by
  refine le_min (le_max_left _ _) ?_
  calc b ≤ c * b := by nlinarith [F.c1]
    _ ≤ c * max b (g * a) := mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [F.c1])

theorem psS_ge (F : Facts c d g) {b a e : ℝ} (hb : 0 ≤ b) : b ≤ psS c b a e := by
  refine le_min (le_max_left _ _) ?_
  calc b ≤ c * b := by nlinarith [F.c1]
    _ ≤ c * max b e := mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [F.c1])

theorem pot_le (c g b : ℝ) (k : HK) : pot c g b k ≤ max b k.time := by
  cases k with
  | T a => exact min_le_left _ _
  | S a e => exact min_le_left _ _

theorem pot_ge (F : Facts c d g) {b : ℝ} (k : HK) (hb : 0 ≤ b) : b ≤ pot c g b k := by
  cases k with
  | T a => exact psT_ge F hb
  | S a e => exact psS_ge F hb

theorem up_mono (F : Facts c d g) : ∀ (l : List ℝ) {y y' : ℝ}, y ≤ y' → up c g l y ≤ up c g l y'
  | [], y, y', h => by
      simp only [up]
      exact mul_le_mul_of_nonneg_left (max_le_max le_rfl h) (by linarith [F.c1])
  | b :: rest, y, y', h => by
      simp only [up]
      exact up_mono F rest (psT_mono F le_rfl
        (mul_le_mul_of_nonneg_left (max_le_max le_rfl h) (by linarith [F.c1])))

/-- Lemma 7.1 does not lower the level value: under `Facts`, for b ≥ 0 and 0 ≤ s ≤ a,
ψ_T(b, a) ≤ ψ_S(max(b, a − s), a, d·s). -/
theorem conv_ineq (F : Facts c d g) {b a s : ℝ} (_hb : 0 ≤ b) (hs : 0 ≤ s) (hsa : s ≤ a) :
    psT c g b a ≤ psS c (max b (a - s)) a (d * s) := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  apply min_le_min
  · exact max_le (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  · apply mul_le_mul_of_nonneg_left _ hc0
    apply max_le (le_trans (le_max_left _ _) (le_max_left _ _))
    by_cases h : g * a ≤ a - s
    · exact le_trans h (le_trans (le_max_right _ _) (le_max_left _ _))
    · push Not at h
      apply le_trans _ (le_max_right _ _)
      have ha : 0 ≤ a := le_trans hs hsa
      have h1 : a * (1 - g) < s := by linarith
      have h2 : d * (a * (1 - g)) ≤ d * s := mul_le_mul_of_nonneg_left h1.le F.d0
      have h3 : g * a ≤ d * (1 - g) * a := mul_le_mul_of_nonneg_right F.dg ha
      nlinarith

/-- Opening a block costs nothing: under `Facts`, for 0 ≤ b ≤ y, y ≤ ψ_T(b, c·max(b, y)). -/
theorem push_ineq (F : Facts c d g) {b y : ℝ} (hb : 0 ≤ b) (hy : b ≤ y) :
    y ≤ psT c g b (c * max b y) := by
  have hc1 := F.c1
  rw [max_eq_right hy]
  have hy0 : 0 ≤ y := le_trans hb hy
  refine le_min (le_trans (by nlinarith) (le_max_right _ _)) ?_
  have : y ≤ c * (g * (c * y)) := by nlinarith [F.c2g]
  exact le_trans this (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))

/-- After the top level opens and closes blocks, the level value seen from the parent:
ψ_T(b', z) ≥ c·max(b', g z) when z ≥ c b'. -/
theorem psT_big (F : Facts c d g) {b z : ℝ} (_hb : 0 ≤ b) (hz : c * b ≤ z) :
    c * max b (g * z) ≤ psT c g b z := by
  have hc1 := F.c1
  have hz0 : 0 ≤ z := le_trans (by nlinarith) hz
  refine le_min ?_ le_rfl
  apply le_trans _ (le_max_right _ _)
  rw [mul_max_of_nonneg _ _ (by linarith : (0:ℝ) ≤ c)]
  exact max_le hz (by nlinarith [F.cg])

/-- Lemma 3.3 (merged) does not lower the level value: under `Facts`, for b ≥ 0, x ≥ 0, e ≥ 0 and
e ≤ a − x, ψ_S(b, a, e) ≤ ψ_T(b', c·max(b', ψ_S(max(b, e), a − x, e))) with b' = max(b, x + e). -/
theorem speed_ineq (F : Facts c d g) {b a e x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (_he : 0 ≤ e)
    (_hex : e ≤ a - x) :
    psS c b a e ≤ psT c g (max b (x + e)) (c * max (max b (x + e)) (psS c (max b e) (a - x) e)) := by
  have hc1 := F.c1
  have hc0 : 0 ≤ c := by linarith
  set b' := max b (x + e) with hb'
  set L := max b e with hL
  have hb'0 : 0 ≤ b' := le_trans hb (le_max_left _ _)
  have hL0 : 0 ≤ L := le_trans hb (le_max_left _ _)
  set Sin := psS c L (a - x) e with hSin
  have hSin0 : L ≤ Sin := psS_ge F hL0
  have hz : c * b' ≤ c * max b' Sin := mul_le_mul_of_nonneg_left (le_max_left _ _) hc0
  refine le_trans ?_ (psT_big F hb'0 hz)
  have hgz : c * max b' (c * g * Sin) ≤ c * max b' (g * (c * max b' Sin)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    apply max_le_max le_rfl
    have : c * g * Sin = g * (c * Sin) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_right _ _) hc0) F.g0
  refine le_trans ?_ hgz
  have hLe : max L e = L := max_eq_left (le_max_right _ _)
  have hSin' : Sin = min (max L (a - x)) (c * L) := by
    simp only [hSin, psS, hLe]
  have hcg0 : 0 ≤ c * g := mul_nonneg hc0 F.g0
  rcases le_total (c * L) (max L (a - x)) with hA | hA
  ·
    rw [hSin', min_eq_right hA]
    have h1 : psS c b a e ≤ c * L := min_le_right _ _
    have h2 : c * L ≤ c * (c * g * (c * L)) := by
      have : c * (c * g * (c * L)) = c * L * (c ^ 2 * g) := by ring
      rw [this]
      have hcL : 0 ≤ c * L := mul_nonneg hc0 hL0
      nlinarith [F.c2g]
    exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left (le_max_right _ _) hc0))
  · rw [hSin', min_eq_left hA]
    rcases le_total a b with hab | hab
    · calc psS c b a e ≤ max b a := min_le_left _ _
        _ = b := max_eq_left hab
        _ ≤ c * b := by nlinarith
        _ ≤ c * max b' (c * g * max L (a - x)) :=
            mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_left _ _)) hc0
    rcases le_total e b with heb | heb
    · calc psS c b a e ≤ c * max b e := min_le_right _ _
        _ = c * b := by rw [max_eq_left heb]
        _ ≤ c * max b' (c * g * max L (a - x)) :=
            mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_left _ _)) hc0
    have hLHS : psS c b a e ≤ min a (c * e) := by
      simp only [psS, max_eq_right hab, max_eq_right heb]; exact le_rfl
    set M' := max (x + e) (c * g * (a - x)) with hM'
    have hM1 : x + e ≤ M' := le_max_left _ _
    have hM2 : c * g * (a - x) ≤ M' := le_max_right _ _
    have hRHS : c * M' ≤ c * max b' (c * g * max L (a - x)) := by
      apply mul_le_mul_of_nonneg_left _ hc0
      apply max_le (le_trans (le_max_right _ _) (le_max_left _ _))
      exact le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hcg0) (le_max_right _ _)
    refine le_trans hLHS (le_trans ?_ hRHS)
    by_cases hcase : e ≤ c * g * a
    ·
      have h1 : c * g * (a + e) ≤ (1 + c * g) * M' := by nlinarith
      have h2 : c * e * (1 + c * g) ≤ c * M' * (1 + c * g) := by nlinarith
      have h3 : c * e ≤ c * M' := le_of_mul_le_mul_right h2 (by linarith)
      exact le_trans (min_le_right _ _) h3
    · push Not at hcase
      have : c * e ≤ c * M' := mul_le_mul_of_nonneg_left (by linarith) hc0
      exact le_trans (min_le_right _ _) this

/-- For c, d ≥ 0, an `RStep` from a line with nonnegative entries leads to such a line. -/
theorem nn_step (hc : 0 ≤ c) (hd : 0 ≤ d) {L L' : RLine} (h : RStep c d L L') (hL : NN L) : NN L' := by
  obtain ⟨hb, hk⟩ := hL
  cases h with
  | convM b rest a s b₁ a₂ e hs hsa h₁ ha he =>
    simp only [KNN] at hk
    have hb0 : 0 ≤ b := hb b (by simp)
    refine ⟨?_, ?_, ?_⟩
    · intro y hy; simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact le_trans (le_trans hb0 (le_max_left _ _)) h₁
      · exact hb y (by simp [hy])
    · linarith
    · nlinarith
  | convN bl a s g' a₂ e hs hsa hg ha he =>
    simp only [KNN] at hk
    have hp : 0 ≤ pin bl := by
      cases bl with
      | nil => simp [pin]
      | cons u _ => exact hb u (by simp)
    refine ⟨?_, ?_, ?_⟩
    · intro y hy; simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact le_trans (le_trans hp (le_max_left _ _)) hg
      · exact hb y hy
    · linarith
    · nlinarith
  | speedM b rest a e x b' L a₂ e₂ hx hex h' hL ha he =>
    simp only [KNN] at hk
    have hb0 : 0 ≤ b := hb b (by simp)
    refine ⟨?_, ?_, ?_⟩
    · intro y hy; simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact le_trans (le_trans hb0 (le_max_left _ _)) hL
      · exact le_trans (le_trans hb0 (le_max_left _ _)) h'
      · exact hb y (by simp [hy])
    · linarith
    · linarith
  | speedN bl a e x g₁ g₂ a₂ e₂ hx hex h₁ h₂ ha he =>
    simp only [KNN] at hk
    have hp : 0 ≤ pin bl := by
      cases bl with
      | nil => simp [pin]
      | cons u _ => exact hb u (by simp)
    refine ⟨?_, ?_, ?_⟩
    · intro y hy; simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact le_trans (le_trans hp (le_max_left _ _)) h₂
      · exact le_trans (le_trans hp (le_max_left _ _)) h₁
      · exact hb y hy
    · linarith
    · linarith
  | slow b rest k a' h =>
    refine ⟨fun y hy => hb y (by simp [hy]), ?_⟩
    simp only [KNN]
    have hb0 : 0 ≤ b := hb b (by simp)
    have : 0 ≤ max (max (pin rest) b) k.time := le_trans hb0 (le_trans (le_max_right _ _) (le_max_left _ _))
    nlinarith

theorem Phi_nonneg (F : Facts c d g) {L : RLine} (hL : NN L) : 0 ≤ Phi c g L := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  obtain ⟨hb, hk⟩ := hL
  rcases L with ⟨bl, k⟩
  cases bl with
  | nil => cases k with
    | T a => simpa [Phi, KNN] using hk
    | S a e => simp [Phi]
  | cons b rest =>
    simp only [Phi]
    have hb0 : 0 ≤ b := hb b (by simp)
    have h0 := pot_ge F k hb0
    have key : ∀ (l : List ℝ), (∀ y ∈ l, 0 ≤ y) → ∀ y, 0 ≤ y → 0 ≤ up c g l y := by
      intro l
      induction l with
      | nil => intro _ y _; simp only [up]; exact mul_nonneg hc0 (le_max_left _ _)
      | cons b' r ih =>
        intro hl y _
        simp only [up]
        have hb'0 : 0 ≤ b' := hl b' (by simp)
        exact ih (fun z hz => hl z (by simp [hz])) _ (le_trans hb'0 (psT_ge F hb'0))
    exact key rest (fun y hy => hb y (by simp [hy])) _ (le_trans hb0 h0)

/-- Under `Facts`, for a ≥ 0 and the parameters of a `convN` step from `([], T a)`
(0 ≤ s ≤ a, max(0, a − s) ≤ g', a ≤ a₂, d·s ≤ e): a ≤ c·max(0, ψ_S(g', a₂, e)). -/
theorem first_ineq (F : Facts c d g) {a s g' a₂ e : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hsa : s ≤ a)
    (hg : max 0 (a - s) ≤ g') (ha₂ : a ≤ a₂) (he : d * s ≤ e) :
    a ≤ c * max 0 (psS c g' a₂ e) := by
  have hc1 := F.c1
  have hc0 : 0 ≤ c := by linarith
  have h1 := conv_ineq F (le_refl 0) hs hsa
  have h2 : psS c (max 0 (a - s)) a (d * s) ≤ psS c g' a₂ e := psS_mono F hg ha₂ he
  have h3 : a ≤ c * psT c g 0 a := by
    simp only [psT, max_eq_right ha]
    rw [max_eq_right (mul_nonneg F.g0 ha)]
    rcases le_total a (c * (g * a)) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith [F.c2g]
  calc a ≤ c * psT c g 0 a := h3
    _ ≤ c * psS c g' a₂ e := mul_le_mul_of_nonneg_left (le_trans h1 h2) hc0
    _ ≤ c * max 0 (psS c g' a₂ e) := mul_le_mul_of_nonneg_left (le_max_right _ _) hc0

/-- Under `Facts c d g`, an `RStep c d` from a line with nonnegative entries does not lower `Phi c g`. -/
theorem phi_step (F : Facts c d g) {L L' : RLine} (h : RStep c d L L') (hL : NN L) :
    Phi c g L ≤ Phi c g L' := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  have hL' := nn_step hc0 F.d0 h hL
  obtain ⟨hb, hk⟩ := hL
  cases h with
  | convM b rest a s b₁ a₂ e hs hsa h₁ ha he =>
    simp only [Phi, pot]
    apply up_mono F
    have hb0 : 0 ≤ b := hb b (by simp)
    exact le_trans (conv_ineq F hb0 hs hsa) (psS_mono F h₁ ha he)
  | convN bl a s g' a₂ e hs hsa hg ha he =>
    simp only [KNN] at hk
    cases bl with
    | nil =>
      simp only [Phi, pot, up]
      exact first_ineq F hk hs hsa (by simpa [pin] using hg) ha he
    | cons b rest =>
      simp only [Phi, pot, up]
      apply up_mono F
      have hb0 : 0 ≤ b := hb b (by simp)
      have hg' : max b (a - s) ≤ g' := by simpa [pin] using hg
      have hY := le_trans (conv_ineq F hb0 hs hsa) (psS_mono F hg' ha he)
      have hbY : b ≤ psS c g' a₂ e :=
        le_trans (le_trans (le_max_left _ _) hg') (psS_ge F (le_trans hb0 (le_trans (le_max_left _ _) hg')))
      exact le_trans hY (push_ineq F hb0 hbY)
  | speedM b rest a e x b' L a₂ e₂ hx hex h' hL ha he =>
    simp only [KNN] at hk
    simp only [Phi, pot, up]
    apply up_mono F
    have hb0 : 0 ≤ b := hb b (by simp)
    refine le_trans (speed_ineq F hb0 hx hk.2 hex) (psT_mono F h' ?_)
    apply mul_le_mul_of_nonneg_left (max_le_max h' (psS_mono F hL ha he)) hc0
  | speedN bl a e x g₁ g₂ a₂ e₂ hx hex h₁ h₂ ha he =>
    simp only [KNN] at hk
    cases bl with
    | nil =>
      simp only [Phi]
      exact Phi_nonneg F hL'
    | cons b rest =>
      simp only [Phi, pot, up]
      apply up_mono F
      have hb0 : 0 ≤ b := hb b (by simp)
      have h₁' : max b (x + e) ≤ g₁ := by simpa [pin] using h₁
      have h₂' : max b e ≤ g₂ := by simpa [pin] using h₂
      have hS := le_trans (speed_ineq F hb0 hx hk.2 hex) (psT_mono F h₁'
        (mul_le_mul_of_nonneg_left (max_le_max h₁' (psS_mono F h₂' ha he)) hc0))
      have hg₁0 : 0 ≤ g₁ := le_trans (le_trans hb0 (le_max_left _ _)) h₁'
      have hbY : b ≤ psT c g g₁ (c * max g₁ (psS c g₂ a₂ e₂)) :=
        le_trans (le_trans (le_max_left _ _) h₁') (psT_ge F hg₁0)
      exact le_trans hS (push_ineq F hb0 hbY)
  | slow b rest k a' hh =>
    have hb0 : 0 ≤ b := hb b (by simp)
    cases rest with
    | nil =>
      simp only [Phi, up, pin] at hh ⊢
      calc c * max 0 (pot c g b k) ≤ c * max (max 0 b) k.time := by
            apply mul_le_mul_of_nonneg_left _ hc0
            rw [max_assoc]; exact max_le_max le_rfl (pot_le c g b k)
        _ ≤ a' := hh
    | cons b' rest' =>
      simp only [Phi, up, pin, pot] at hh ⊢
      apply up_mono F
      apply psT_mono F le_rfl
      calc c * max b' (pot c g b k) ≤ c * max (max b' b) k.time := by
            apply mul_le_mul_of_nonneg_left _ hc0
            rw [max_assoc]; exact max_le_max le_rfl (pot_le c g b k)
        _ ≤ a' := hh

/-- Under `Facts c d g`: along an `RPath c d M n` from `M 0 = ([], T a₀)` with a₀ ≥ 0 to
`M n = ([], T a')`, a₀ ≤ a'. -/
theorem qf_ge (F : Facts c d g) {M : ℕ → RLine} {n : ℕ} (hp : RPath c d M n) {a₀ a' : ℝ}
    (ha₀ : 0 ≤ a₀) (h0 : M 0 = ([], .T a₀)) (hN : M n = ([], .T a')) : a₀ ≤ a' := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  have hnn : ∀ i ≤ n, NN (M i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ⟨by simp, by simpa [KNN] using ha₀⟩
    | succ j ih => intro hj; exact nn_step hc0 F.d0 (hp j (by omega)) (ih (by omega))
  have hmono : ∀ i ≤ n, Phi c g (M 0) ≤ Phi c g (M i) := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ j ih => intro hj; exact le_trans (ih (by omega)) (phi_step F (hp j (by omega)) (hnn j (by omega)))
  have := hmono n le_rfl
  rw [h0, hN] at this
  simpa [Phi] using this

end lemmas

def encK : HY.Ker → HK
  | .T a => .T a
  | .S a e => .S a e

/-- The relaxed encoding of a line: the output superscripts and the kernel. -/
def enc (L : HY.Line) : RLine := (L.1.map HY.Blk.o, encK L.2)

theorem encK_time (k : HY.Ker) : (encK k).time = k.time := by cases k <;> rfl

theorem pin_le (bl : List HY.Blk) : pin (bl.map HY.Blk.o) ≤ HY.pin bl := by
  cases bl <;> simp [pin, HY.pin]

theorem pin_eq_cons (u : HY.Blk) (rest : List HY.Blk) : pin ((u :: rest).map HY.Blk.o) = u.o := rfl

/-- For c ≥ 0, every `HY.Step c d L L'` gives `RStep c d (enc L) (enc L')`. -/
theorem sim {c d : ℝ} (hc : 0 ≤ c) {L L' : HY.Line} (h : HY.Step c d L L') :
    RStep c d (enc L) (enc L') := by
  cases h with
  | convMerge u rest a s hs hsa hb =>
    exact RStep.convM u.o (rest.map HY.Blk.o) a s (max (a - s) u.o) a (d * s) hs.le hsa
      (by rw [max_comm]) le_rfl le_rfl
  | convNew bl q a s hq hs hsa hb =>
    exact RStep.convN (bl.map HY.Blk.o) a s (max (a - s) (HY.pin bl)) a (d * s) hs.le hsa
      (max_le (le_trans (pin_le bl) (le_max_right _ _)) (le_max_left _ _)) le_rfl le_rfl
  | speedMerge u rest a e x ha he hex hx hx1 hb =>
    exact RStep.speedM u.o (rest.map HY.Blk.o) a e x (max u.o (x + e)) (max u.o e) (a - x) e hx hex
      le_rfl le_rfl le_rfl le_rfl
  | speedNew bl q a e x hq ha he hex hx hx1 hb =>
    exact RStep.speedN (bl.map HY.Blk.o) a e x (max (HY.pin bl) (x + e)) (max (HY.pin bl) e) (a - x) e
      hx hex (max_le_max (pin_le bl) le_rfl) (max_le_max (pin_le bl) le_rfl) le_rfl le_rfl
  | slow u rest k h1 h2 h3 h4 =>
    show RStep c d (u.o :: rest.map HY.Blk.o, encK k) (rest.map HY.Blk.o, .T _)
    apply RStep.slow
    apply mul_le_mul_of_nonneg_left _ hc
    rw [encK_time]
    exact max_le_max (max_le_max (pin_le rest) le_rfl) (le_max_right _ _)

/-- For real d > 0, c ≥ 1 and c² ≥ 1 + 1/d there is no strict normal-form proof `HY.NF c d M n`. -/
theorem no_nf {c d : ℝ} (hd : 0 < d) (hc : 1 ≤ c) (hcd : 1 + 1 / d ≤ c ^ 2) (M : ℕ → HY.Line) (n : ℕ) :
    ¬ HY.NF c d M n := by
  rintro ⟨hn, hp, ⟨a₀, h0⟩, ⟨a', hN⟩, _, h1, hlt, _⟩
  set A := max (1 + 1 / d) c with hA
  have hA1 : 1 + 1 / d ≤ A := le_max_left _ _
  have hAc : c ≤ A := le_max_right _ _
  have hApos : 0 < A := by linarith
  have hAc2 : A ≤ c ^ 2 := max_le hcd (by nlinarith)
  have F : Facts c d (1 / A) := by
    refine ⟨hc, by positivity, ?_, ?_, hd.le, ?_⟩
    · rw [mul_one_div, div_le_one hApos]; exact hAc
    · rw [mul_one_div, le_div_iff₀ hApos]; linarith
    · have hd1 : 1 / d ≤ A - 1 := by linarith
      have : 1 ≤ d * (A - 1) := by
        rw [div_le_iff₀ hd] at hd1; linarith
      rw [show d * (1 - 1 / A) = d * (A - 1) / A by field_simp]
      rw [div_le_div_iff_of_pos_right hApos]; exact this
  have hrp : RPath c d (fun i => enc (M i)) n := fun i hi => sim (by linarith) (hp i hi)
  have hT0 : (M 0).2.time = a₀ := by rw [h0]; rfl
  have hTn : (M n).2.time = a' := by rw [hN]; rfl
  have ha₀ : 0 ≤ a₀ := by rw [← hT0]; linarith
  have := qf_ge F hrp ha₀ (by show enc (M 0) = _; rw [h0]; rfl) (by show enc (M n) = _; rw [hN]; rfl)
  rw [hT0, hTn] at hlt
  linarith

end HL
end PastaMath.OneTapeThreshold
