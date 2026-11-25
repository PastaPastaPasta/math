-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Relaxed
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Multi-level potentials for the relaxed calculus

A potential for `HL.RStep` built from a finite list `lv` of levels (P_j, θ_j) together with level 0,
(0, θ₀). With κ_p = max(c, P_p) (`kap`):

* T-levels: ψ_T(b, a) = min(max(b, a), max(c·b, Tm(b, a))), where
  Tm(b, a) = min over the levels of max(P_j·b, θ_j·a/c) (level 0 contributes θ₀·a/c);
* S-levels: ψ_S(b, a, e) = inf over words w (lists of levels, outermost first) of max(0, V_w(b, a, e)),
  with V_[](b, a, e) = max(b, a) and
  V_{p::w}(b, a, e) = max(κ_p·b, θ_p·Ad(w)·max(b, e), (a + |p::w|·e)/D(p::w)),
  Ad([]) = 1, Ad(p::w) = max(κ_p, θ_p·Ad(w)), D([]) = 1, D(p::w) = 1/κ_p + D(w)/θ_p;
* a line's value `Phi` lifts the innermost level through each outer block of superscript b' by
  y ↦ ψ_T(b', c·max(b', y)) and finally by y ↦ c·max(0, y); `Phi ([], T a) = a`.

`Base c d θ₀ lv`: 1 ≤ c, 0 ≤ d, and every level (level 0 included) has 1 ≤ θ ≤ c and P ≥ 0.
`Hyp c d θ₀ lv` adds the Lemma 7.1 condition `ConvOK` for the state (Ad w, AL w, D w, |w|) of every
nonempty word w over the levels, where AL([]) = 0, AL(p::w) = θ_p·Ad(w), and
`ConvOK c d θ₀ lv A L D m` says Tm(b, a) ≤ max(A·b, Qf·a) for all b, a ≥ 0, with
Qf = max(A·L·d/(A + L·d), A·(1 + m·d)/(A·D + m·d)).

Under `Hyp`, `phi_step` shows that Phi does not decrease along an `RStep` from a line with
nonnegative entries. Lemma 3.3 is handled by `V_succ` (prepending a letter to a word absorbs one
speedup) and needs only `Base`; Lemma 7.1 is `conv_word`, which reduces the inequality for a word to
`ConvOK` by two weighted averages (`cross`). Consequences: `qf_ge` (every quantifier-free line
`T a'` reached from `T a₀`, a₀ ≥ 0, has a₀ ≤ a'), `no_nf` (no `HY.NF` proof at c), and, when
every θ (level 0 included) is > 1 and c > 1, `qf_gt` and `no_nf_le` (a₀ < a' along every path of
length ≥ 1 from `T a₀`, a₀ > 0, to `T a'`).

`rstep_mono`: an `RStep` at c from a line with nonnegative entries is an `RStep` at every c₀ ≤ c
(only `slow` depends on c, and its bound only weakens). `rge_of`, `rgt_of`, `no_nf_of` and
`no_nf_le_of` transfer a potential valid at c₀ to every c ≥ c₀.
-/

namespace PastaMath.OneTapeThreshold
namespace HLM

open HL

noncomputable section

/-- κ_p = max(c, P_p) for a level p = (P_p, θ_p). -/
def kap (c : ℝ) (p : ℝ × ℝ) : ℝ := max c p.1

/-- Tm(b, a) = min over the levels of `lv` of max(P·b, θ·a/c), together with level 0's term θ₀·a/c. -/
def Tm (c θ₀ : ℝ) (lv : List (ℝ × ℝ)) (b a : ℝ) : ℝ :=
  lv.foldr (fun p acc => min (max (p.1 * b) (p.2 / c * a)) acc) (θ₀ / c * a)

/-- ψ_T(b, a) = min(max(b, a), max(c·b, Tm(b, a))). -/
def psT (c θ₀ : ℝ) (lv : List (ℝ × ℝ)) (b a : ℝ) : ℝ := min (max b a) (max (c * b) (Tm c θ₀ lv b a))

/-- Ad([]) = 1, Ad(p :: w) = max(κ_p, θ_p·Ad(w)). -/
def Ad (c : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 1
  | p :: w => max (kap c p) (p.2 * Ad c w)

/-- AL([]) = 0, AL(p :: w) = θ_p·Ad(w). -/
def AL (c : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | p :: w => p.2 * Ad c w

/-- D([]) = 1, D(p :: w) = 1/κ_p + D(w)/θ_p. -/
def Dw (c : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 1
  | p :: w => 1 / kap c p + Dw c w / p.2

/-- U_w(a, e) = (a + |w|·e)/D(w). -/
def Uw (c : ℝ) (w : List (ℝ × ℝ)) (a e : ℝ) : ℝ := (a + (w.length : ℝ) * e) / Dw c w

/-- V_[](b, a, e) = max(b, a); V_{p::w}(b, a, e) = max(κ_p·b, θ_p·Ad(w)·max(b, e), U_{p::w}(a, e)). -/
def V (c : ℝ) : List (ℝ × ℝ) → ℝ → ℝ → ℝ → ℝ
  | [], b, a, _ => max b a
  | p :: w, b, a, e => max (kap c p * b) (max (p.2 * Ad c w * max b e) (Uw c (p :: w) a e))

/-- Every letter of the word is level 0, (0, θ₀), or a level of `lv`. -/
def Wd (θ₀ : ℝ) (lv : List (ℝ × ℝ)) (w : List (ℝ × ℝ)) : Prop := ∀ p ∈ w, p ∈ (0, θ₀) :: lv

/-- Words over the levels (level 0 included). -/
abbrev Word (θ₀ : ℝ) (lv : List (ℝ × ℝ)) := {w : List (ℝ × ℝ) // Wd θ₀ lv w}

instance (θ₀ : ℝ) (lv : List (ℝ × ℝ)) : Nonempty (Word θ₀ lv) := ⟨⟨[], by simp [Wd]⟩⟩

/-- ψ_S(b, a, e) = inf over words w of max(0, V_w(b, a, e)). -/
def psS (c θ₀ : ℝ) (lv : List (ℝ × ℝ)) (b a e : ℝ) : ℝ := ⨅ w : Word θ₀ lv, max 0 (V c w.1 b a e)

/-- Qf(d, A, L, D, m) = max(A·L·d/(A + L·d), A·(1 + m·d)/(A·D + m·d)). -/
def Qf (d A L D : ℝ) (m : ℕ) : ℝ := max (A * L * d / (A + L * d)) (A * (1 + m * d) / (A * D + m * d))

/-- The Lemma 7.1 condition for a word with state (A, L, D, m): Tm(b, a) ≤ max(A·b, Qf·a) for all
b, a ≥ 0. -/
def ConvOK (c d θ₀ : ℝ) (lv : List (ℝ × ℝ)) (A L D : ℝ) (m : ℕ) : Prop :=
  ∀ b a : ℝ, 0 ≤ b → 0 ≤ a → Tm c θ₀ lv b a ≤ max (A * b) (Qf d A L D m * a)

/-- 1 ≤ c, 0 ≤ d, and every level p of (0, θ₀) :: lv has 1 ≤ θ_p ≤ c and 0 ≤ P_p. -/
structure Base (c d θ₀ : ℝ) (lv : List (ℝ × ℝ)) : Prop where
  c1 : 1 ≤ c
  d0 : 0 ≤ d
  t1 : ∀ p ∈ (0, θ₀) :: lv, 1 ≤ p.2
  tc : ∀ p ∈ (0, θ₀) :: lv, p.2 ≤ c
  P0 : ∀ p ∈ (0, θ₀) :: lv, 0 ≤ p.1

/-- `Base` and, for every nonempty word w over the levels, `ConvOK` for the state
(Ad w, AL w, D w, |w|). -/
structure Hyp (c d θ₀ : ℝ) (lv : List (ℝ × ℝ)) : Prop extends Base c d θ₀ lv where
  conv : ∀ w, Wd θ₀ lv w → w ≠ [] → ConvOK c d θ₀ lv (Ad c w) (AL c w) (Dw c w) w.length

def pot (c θ₀ : ℝ) (lv : List (ℝ × ℝ)) (b : ℝ) : HK → ℝ
  | .T a => psT c θ₀ lv b a
  | .S a e => psS c θ₀ lv b a e

/-- Lifts a level value y through the outer superscripts: y ↦ ψ_T(b', c·max(b', y)) for each outer b',
then y ↦ c·max(0, y). -/
def up (c θ₀ : ℝ) (lv : List (ℝ × ℝ)) : List ℝ → ℝ → ℝ
  | [], y => c * max 0 y
  | b :: rest, y => up c θ₀ lv rest (psT c θ₀ lv b (c * max b y))

/-- The potential of a line: `a` for `([], T a)`, 0 for `([], S a e)`, and the lifted value of the
innermost level otherwise. -/
def Phi (c θ₀ : ℝ) (lv : List (ℝ × ℝ)) : RLine → ℝ
  | ([], .T a) => a
  | ([], .S _ _) => 0
  | (b :: rest, k) => up c θ₀ lv rest (pot c θ₀ lv b k)

section lemmas

variable {c d θ₀ : ℝ} {lv : List (ℝ × ℝ)}

theorem c0 (H : Base c d θ₀ lv) : 0 < c := by linarith [H.c1]

theorem kap_ge (c : ℝ) (p : ℝ × ℝ) : c ≤ kap c p := le_max_left _ _

theorem kap_pos (H : Base c d θ₀ lv) (p : ℝ × ℝ) : 0 < kap c p := lt_of_lt_of_le (c0 H) (kap_ge c p)

theorem kap_mul (_H : Base c d θ₀ lv) {p : ℝ × ℝ} (_hp : 0 ≤ p.1) {b : ℝ} (hb : 0 ≤ b) :
    max (c * b) (p.1 * b) = kap c p * b := by
  unfold kap; rw [max_mul_of_nonneg _ _ hb]

theorem th_pos (H : Base c d θ₀ lv) {p : ℝ × ℝ} (hp : p ∈ (0, θ₀) :: lv) : 0 < p.2 := by
  linarith [H.t1 p hp]

theorem wd_cons {p : ℝ × ℝ} {w : List (ℝ × ℝ)} (h : Wd θ₀ lv (p :: w)) :
    p ∈ (0, θ₀) :: lv ∧ Wd θ₀ lv w :=
  ⟨h p (by simp), fun q hq => h q (by simp [hq])⟩

theorem Ad_ge_one (H : Base c d θ₀ lv) : ∀ w, Wd θ₀ lv w → 1 ≤ Ad c w
  | [], _ => by simp [Ad]
  | p :: w, h => by
      simp only [Ad]
      exact le_trans (le_trans H.c1 (kap_ge c p)) (le_max_left _ _)

theorem Ad_pos (H : Base c d θ₀ lv) {w} (h : Wd θ₀ lv w) : 0 < Ad c w := by
  linarith [Ad_ge_one H w h]

theorem Dw_pos (H : Base c d θ₀ lv) : ∀ w, Wd θ₀ lv w → 0 < Dw c w
  | [], _ => by simp [Dw]
  | p :: w, h => by
      simp only [Dw]
      obtain ⟨hp, hw⟩ := wd_cons h
      have := Dw_pos H w hw
      have h1 : 0 < 1 / kap c p := div_pos one_pos (kap_pos H p)
      have h2 : 0 ≤ Dw c w / p.2 := div_nonneg this.le (th_pos H hp).le
      linarith

theorem AL_le_Ad (_H : Base c d θ₀ lv) : ∀ w, Wd θ₀ lv w → AL c w ≤ Ad c w
  | [], h => by simp [AL, Ad]
  | p :: w, _ => by simp only [AL, Ad]; exact le_max_right _ _

theorem AL_nonneg (H : Base c d θ₀ lv) : ∀ w, Wd θ₀ lv w → 0 ≤ AL c w
  | [], _ => by simp [AL]
  | p :: w, h => by
      simp only [AL]
      obtain ⟨hp, hw⟩ := wd_cons h
      exact mul_nonneg (th_pos H hp).le (Ad_pos H hw).le

/-- Under `Base`, Ad(w)·D(w) ≥ 1 for every word w over the levels. -/
theorem AdDw_ge_one (H : Base c d θ₀ lv) : ∀ w, Wd θ₀ lv w → 1 ≤ Ad c w * Dw c w
  | [], _ => by simp [Ad, Dw]
  | p :: w, h => by
      simp only [Ad, Dw]
      obtain ⟨hp, hw⟩ := wd_cons h
      have hk := kap_pos H p
      have hD := Dw_pos H w hw
      have hθ := th_pos H hp
      have h1 : 1 ≤ kap c p * (1 / kap c p + Dw c w / p.2) := by
        rw [mul_add, mul_one_div_cancel hk.ne']
        have : 0 ≤ kap c p * (Dw c w / p.2) := mul_nonneg hk.le (div_nonneg hD.le hθ.le)
        linarith
      exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by have := div_pos one_pos hk; have := div_nonneg hD.le hθ.le; linarith))

/-- Under `Base`, for a letter p and a word w over the levels and all real a, e, x:
U_{p::w}(a, e) ≤ max(κ_p·(x + e), θ_p·U_w(a − x, e)). -/
theorem U_succ (H : Base c d θ₀ lv) {p : ℝ × ℝ} (hp : p ∈ (0, θ₀) :: lv) {w : List (ℝ × ℝ)}
    (hw : Wd θ₀ lv w) (a e x : ℝ) :
    Uw c (p :: w) a e ≤ max (kap c p * (x + e)) (p.2 * Uw c w (a - x) e) := by
  set M := max (kap c p * (x + e)) (p.2 * Uw c w (a - x) e)
  have hk := kap_pos H p
  have hθ := th_pos H hp
  have hD := Dw_pos H w hw
  have hD1 := Dw_pos H (p :: w) (fun q hq => by
    simp only [List.mem_cons] at hq; rcases hq with rfl | hq; exact hp; exact hw q hq)
  have h1 : kap c p * (x + e) ≤ M := le_max_left _ _
  have h2 : p.2 * Uw c w (a - x) e ≤ M := le_max_right _ _
  have i1 : x + e ≤ M / kap c p := by rw [le_div_iff₀ hk]; linarith [mul_comm (kap c p) (x + e)]
  have i2 : a - x + w.length * e ≤ Dw c w / p.2 * M := by
    have : Uw c w (a - x) e = (a - x + w.length * e) / Dw c w := rfl
    rw [this] at h2
    have h3 : (a - x + w.length * e) ≤ Dw c w * (M / p.2) := by
      rw [← div_le_iff₀' hD]
      rw [le_div_iff₀ hθ]; linarith [mul_comm p.2 ((a - x + w.length * e) / Dw c w)]
    calc a - x + w.length * e ≤ Dw c w * (M / p.2) := h3
      _ = Dw c w / p.2 * M := by ring
  unfold Uw
  rw [div_le_iff₀ hD1]
  simp only [Dw, List.length_cons]
  push_cast
  have : M / kap c p = 1 / kap c p * M := by ring
  nlinarith

theorem V_ge_Ad (H : Base c d θ₀ lv) : ∀ w, Wd θ₀ lv w → ∀ {L a e : ℝ}, 0 ≤ L → Ad c w * L ≤ V c w L a e
  | [], _, L, a, e, hL => by simp only [Ad, V, one_mul]; exact le_max_left _ _
  | p :: w, h, L, a, e, hL => by
      obtain ⟨hp, hw⟩ := wd_cons h
      simp only [Ad, V]
      rw [max_mul_of_nonneg _ _ hL]
      refine max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
      refine le_trans ?_ (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (mul_nonneg (th_pos H hp).le (Ad_pos H hw).le)

theorem Uw_le_V : ∀ w : List (ℝ × ℝ), ∀ {L a e : ℝ}, Uw c w a e ≤ V c w L a e
  | [], L, a, e => by simp only [Uw, V, Dw, List.length_nil]; simp
  | p :: w, L, a, e => by simp only [V]; exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- Prepending a letter absorbs one Lemma 3.3 step: under `Base`, for a letter p, a word w,
b ≥ 0 and x ≥ 0, V_{p::w}(b, a, e) ≤ max(κ_p·max(b, x + e), θ_p·V_w(max(b, e), a − x, e)). -/
theorem V_succ (H : Base c d θ₀ lv) {p : ℝ × ℝ} (hp : p ∈ (0, θ₀) :: lv) {w : List (ℝ × ℝ)}
    (hw : Wd θ₀ lv w) {b a e x : ℝ} (hb : 0 ≤ b) (_hx : 0 ≤ x) :
    V c (p :: w) b a e ≤ max (kap c p * max b (x + e)) (p.2 * V c w (max b e) (a - x) e) := by
  have hk := kap_pos H p
  have hθ := th_pos H hp
  simp only [V]
  refine max_le ?_ (max_le ?_ ?_)
  · exact le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hk.le) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (V_ge_Ad H w hw (le_trans hb (le_max_left _ _))) hθ.le
  · refine le_trans (U_succ H hp hw a e x) (max_le_max ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hk.le
    · exact mul_le_mul_of_nonneg_left (Uw_le_V w) hθ.le

theorem V_mono (H : Base c d θ₀ lv) : ∀ w, Wd θ₀ lv w → ∀ {b b' a a' e e' : ℝ}, b ≤ b' → a ≤ a' →
    e ≤ e' → V c w b a e ≤ V c w b' a' e'
  | [], _, _, _, _, _, _, _, hb, ha, _ => by simp only [V]; exact max_le_max hb ha
  | p :: w, h, _, _, _, _, _, _, hb, ha, he => by
      obtain ⟨hp, hw⟩ := wd_cons h
      have hD1 := Dw_pos H (p :: w) h
      simp only [V]
      refine max_le_max (mul_le_mul_of_nonneg_left hb (kap_pos H p).le) (max_le_max ?_ ?_)
      · exact mul_le_mul_of_nonneg_left (max_le_max hb he)
          (mul_nonneg (th_pos H hp).le (Ad_pos H hw).le)
      · unfold Uw
        apply div_le_div_of_nonneg_right _ hD1.le
        have : ((p :: w).length : ℝ) * _ ≤ ((p :: w).length : ℝ) * _ :=
          mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
        linarith

theorem V_ge (H : Base c d θ₀ lv) : ∀ w, Wd θ₀ lv w → ∀ {b a e : ℝ}, 0 ≤ b → b ≤ V c w b a e
  | [], _, b, a, e, _ => le_max_left _ _
  | p :: w, _, b, a, e, hb => by
      simp only [V]
      refine le_trans ?_ (le_max_left _ _)
      have : 1 ≤ kap c p := le_trans H.c1 (kap_ge c p)
      nlinarith

theorem bdd (b a e : ℝ) : BddBelow (Set.range fun w : Word θ₀ lv => max 0 (V c w.1 b a e)) :=
  ⟨0, by rintro _ ⟨w, rfl⟩; exact le_max_left _ _⟩

theorem psS_le (b a e : ℝ) (w : Word θ₀ lv) : psS c θ₀ lv b a e ≤ max 0 (V c w.1 b a e) :=
  ciInf_le (bdd b a e) w

theorem le_psS {y b a e : ℝ} (h : ∀ w : Word θ₀ lv, y ≤ max 0 (V c w.1 b a e)) : y ≤ psS c θ₀ lv b a e :=
  le_ciInf h

theorem psS_mono (H : Base c d θ₀ lv) {b b' a a' e e' : ℝ} (hb : b ≤ b') (ha : a ≤ a') (he : e ≤ e') :
    psS c θ₀ lv b a e ≤ psS c θ₀ lv b' a' e' :=
  le_psS fun w => le_trans (psS_le b a e w) (max_le_max le_rfl (V_mono H w.1 w.2 hb ha he))

theorem psS_ge (H : Base c d θ₀ lv) {b a e : ℝ} (hb : 0 ≤ b) : b ≤ psS c θ₀ lv b a e :=
  le_psS fun w => le_trans (V_ge H w.1 w.2 hb) (le_max_right _ _)

theorem psS_le_max {b a e : ℝ} (hb : 0 ≤ b) : psS c θ₀ lv b a e ≤ max b a := by
  have h := psS_le (c := c) (θ₀ := θ₀) (lv := lv) b a e ⟨[], by simp [Wd]⟩
  simp only [V] at h
  rwa [max_eq_right (le_trans hb (le_max_left _ _))] at h

theorem Tm_le_base (b a : ℝ) : Tm c θ₀ lv b a ≤ θ₀ / c * a := by
  unfold Tm
  induction lv with
  | nil => simp
  | cons p rest ih => simp only [List.foldr_cons]; exact le_trans (min_le_right _ _) ih

theorem Tm_le_mem {p : ℝ × ℝ} (hp : p ∈ lv) (b a : ℝ) : Tm c θ₀ lv b a ≤ max (p.1 * b) (p.2 / c * a) := by
  unfold Tm
  induction lv with
  | nil => simp at hp
  | cons q rest ih =>
    simp only [List.foldr_cons]
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih hp)

/-- Tm is ≤ the term of any letter (level 0 included). -/
theorem Tm_le_letter {p : ℝ × ℝ} (hp : p ∈ (0, θ₀) :: lv) {b a : ℝ} (_ha : 0 ≤ a) :
    Tm c θ₀ lv b a ≤ max (p.1 * b) (p.2 / c * a) := by
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · refine le_trans (Tm_le_base b a) (le_max_right _ _)
  · exact Tm_le_mem hp b a

/-- Lower bound for Tm from lower bounds for each letter. -/
theorem le_Tm {y b a : ℝ} (h0 : y ≤ θ₀ / c * a) (h : ∀ p ∈ lv, y ≤ max (p.1 * b) (p.2 / c * a)) :
    y ≤ Tm c θ₀ lv b a := by
  unfold Tm
  induction lv with
  | nil => simpa using h0
  | cons q rest ih =>
    simp only [List.foldr_cons]
    exact le_min (h q (by simp)) (ih (fun p hp => h p (by simp [hp])))

theorem le_max_foldr {y x : ℝ} (f : ℝ × ℝ → ℝ) (base : ℝ) :
    ∀ l : List (ℝ × ℝ), y ≤ max x base → (∀ p ∈ l, y ≤ max x (f p)) →
      y ≤ max x (l.foldr (fun p acc => min (f p) acc) base)
  | [], h0, _ => by simpa using h0
  | q :: rest, h0, hl => by
      simp only [List.foldr_cons]
      rw [max_min_distrib_left]
      exact le_min (hl q (by simp)) (le_max_foldr f base rest h0 (fun p hp => hl p (by simp [hp])))

theorem le_max_Tm (H : Base c d θ₀ lv) {y b W : ℝ} (hb : 0 ≤ b)
    (h : ∀ p ∈ (0, θ₀) :: lv, y ≤ max (kap c p * b) (p.2 * W)) : y ≤ max (c * b) (Tm c θ₀ lv b (c * W)) := by
  have hc := c0 H
  have e1 : ∀ θ : ℝ, θ / c * (c * W) = θ * W := fun θ => by field_simp
  unfold Tm
  apply le_max_foldr
  · have h0 := h (0, θ₀) (by simp)
    have : kap c (0, θ₀) = c := max_eq_left hc.le
    rw [this] at h0
    rw [e1]; exact h0
  · intro p hp
    have := h p (by simp [hp])
    rw [e1, ← max_assoc, kap_mul H (H.P0 p (by simp [hp])) hb]
    exact this

theorem psT_mono (H : Base c d θ₀ lv) {b b' a a' : ℝ} (hb : b ≤ b') (ha : a ≤ a') :
    psT c θ₀ lv b a ≤ psT c θ₀ lv b' a' := by
  have hc := c0 H
  unfold psT
  refine min_le_min (max_le_max hb ha) (max_le_max (mul_le_mul_of_nonneg_left hb hc.le) ?_)
  apply le_Tm
  · exact le_trans (Tm_le_base b a) (mul_le_mul_of_nonneg_left ha (div_nonneg (by linarith [H.t1 (0, θ₀) (by simp)]) hc.le))
  · intro p hp
    refine le_trans (Tm_le_mem hp b a) (max_le_max ?_ ?_)
    · exact mul_le_mul_of_nonneg_left hb (H.P0 p (by simp [hp]))
    · exact mul_le_mul_of_nonneg_left ha (div_nonneg (by linarith [H.t1 p (by simp [hp])]) hc.le)

theorem Tm_ge (H : Base c d θ₀ lv) {b a : ℝ} (_hb : 0 ≤ b) (ha : 0 ≤ a) : a / c ≤ Tm c θ₀ lv b a := by
  have hc := c0 H
  apply le_Tm
  · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
    nlinarith [H.t1 (0, θ₀) (by simp)]
  · intro p hp
    refine le_trans ?_ (le_max_right _ _)
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
    nlinarith [H.t1 p (by simp [hp])]

theorem psT_ge (H : Base c d θ₀ lv) {b a : ℝ} (hb : 0 ≤ b) : b ≤ psT c θ₀ lv b a := by
  refine le_min (le_max_left _ _) (le_trans ?_ (le_max_left _ _))
  nlinarith [H.c1]

theorem pot_le (_H : Base c d θ₀ lv) (b : ℝ) (k : HK) (hb : 0 ≤ b) : pot c θ₀ lv b k ≤ max b k.time := by
  cases k with
  | T a => exact min_le_left _ _
  | S a e => exact psS_le_max hb

theorem pot_ge (H : Base c d θ₀ lv) {b : ℝ} (k : HK) (hb : 0 ≤ b) : b ≤ pot c θ₀ lv b k := by
  cases k with
  | T a => exact psT_ge H hb
  | S a e => exact psS_ge H hb

theorem up_mono (H : Base c d θ₀ lv) : ∀ (l : List ℝ) {y y' : ℝ}, y ≤ y' → up c θ₀ lv l y ≤ up c θ₀ lv l y'
  | [], y, y', h => by
      simp only [up]
      exact mul_le_mul_of_nonneg_left (max_le_max le_rfl h) (c0 H).le
  | b :: rest, y, y', h => by
      simp only [up]
      exact up_mono H rest (psT_mono H le_rfl
        (mul_le_mul_of_nonneg_left (max_le_max le_rfl h) (c0 H).le))

/-- Under `Base`, for 0 ≤ b ≤ W: if y ≤ max(κ_p·b, θ_p·W) for every level p, then
y ≤ ψ_T(b, c·W). -/
theorem le_psT_lift (H : Base c d θ₀ lv) {y b W : ℝ} (hb : 0 ≤ b) (hbW : b ≤ W)
    (h : ∀ p ∈ (0, θ₀) :: lv, y ≤ max (kap c p * b) (p.2 * W)) : y ≤ psT c θ₀ lv b (c * W) := by
  have hc := c0 H
  refine le_min ?_ (le_max_Tm H hb h)
  have h0 := h (0, θ₀) (by simp)
  refine le_trans h0 (le_trans (max_le ?_ ?_) (le_max_right _ _))
  · simp only [kap]
    have : max c 0 = c := max_eq_left hc.le
    rw [this]; exact mul_le_mul_of_nonneg_left hbW hc.le
  · have hW : 0 ≤ W := le_trans hb hbW
    exact mul_le_mul_of_nonneg_right (H.tc (0, θ₀) (by simp)) hW

/-- Opening a block costs nothing: under `Base`, for 0 ≤ b ≤ y, y ≤ ψ_T(b, c·max(b, y)). -/
theorem push_ineq (H : Base c d θ₀ lv) {b y : ℝ} (hb : 0 ≤ b) (hy : b ≤ y) :
    y ≤ psT c θ₀ lv b (c * max b y) := by
  rw [max_eq_right hy]
  apply le_psT_lift H hb hy
  intro p hp
  refine le_trans ?_ (le_max_right _ _)
  have := H.t1 p hp
  nlinarith

/-- Lemma 3.3 (merged) does not lower the level value: under `Base`, for b ≥ 0 and x ≥ 0,
ψ_S(b, a, e) ≤ ψ_T(b', c·max(b', ψ_S(max(b, e), a − x, e))) with b' = max(b, x + e). -/
theorem speed_ineq (H : Base c d θ₀ lv) {b a e x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) :
    psS c θ₀ lv b a e ≤
      psT c θ₀ lv (max b (x + e)) (c * max (max b (x + e)) (psS c θ₀ lv (max b e) (a - x) e)) := by
  set b' := max b (x + e)
  set W := psS c θ₀ lv (max b e) (a - x) e
  have hb'0 : 0 ≤ b' := le_trans hb (le_max_left _ _)
  apply le_psT_lift H hb'0 (le_max_left _ _)
  intro p hp
  have hθ := th_pos H hp
  rcases le_or_gt (psS c θ₀ lv b a e) (kap c p * b') with h | h
  · exact le_trans h (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_right b' W) hθ.le)
    have : psS c θ₀ lv b a e / p.2 ≤ W := by
      apply le_psS
      intro w
      have hpw : Wd θ₀ lv (p :: w.1) := fun q hq => by
        simp only [List.mem_cons] at hq; rcases hq with rfl | hq; exact hp; exact w.2 q hq
      have h1 := psS_le (c := c) b a e ⟨p :: w.1, hpw⟩
      have h2 := V_succ H hp w.2 (b := b) (a := a) (e := e) hb hx
      have hV0 : 0 ≤ V c (p :: w.1) b a e := le_trans hb (V_ge H _ hpw hb)
      simp only at h1
      rw [max_eq_right hV0] at h1
      have h3 : psS c θ₀ lv b a e ≤ p.2 * V c w.1 (max b e) (a - x) e := by
        rcases le_total (kap c p * b') (p.2 * V c w.1 (max b e) (a - x) e) with h4 | h4
        · exact le_trans h1 (le_trans h2 (by rw [max_eq_right h4]))
        · exfalso
          have := le_trans h1 (le_trans h2 (by rw [max_eq_left h4]))
          linarith
      rw [div_le_iff₀ hθ]
      exact le_trans h3 (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hθ.le)
    rw [div_le_iff₀ hθ] at this
    linarith [mul_comm W p.2]

/-- For d ≥ 0, A > 0, L ≥ 0, D > 0, a ≥ 0 and every real s:
Qf(d, A, L, D, m)·a ≤ max(A·(a − s), L·d·s, (a + m·d·s)/D). -/
theorem cross (hd : 0 ≤ d) {A L D a s : ℝ} (m : ℕ) (hA : 0 < A) (hL : 0 ≤ L) (hD : 0 < D) (ha : 0 ≤ a) :
    Qf d A L D m * a ≤ max (A * (a - s)) (max (L * d * s) ((a + m * (d * s)) / D)) := by
  set M := max (A * (a - s)) (max (L * d * s) ((a + m * (d * s)) / D))
  have h1 : A * (a - s) ≤ M := le_max_left _ _
  have h2 : L * d * s ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have h3 : (a + m * (d * s)) / D ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold Qf
  rw [max_mul_of_nonneg _ _ ha]
  apply max_le
  · have hpos : 0 < A + L * d := by have := mul_nonneg hL hd; linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have : (L * d) * (A * (a - s)) + A * (L * d * s) = A * L * d * a := by ring
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hL hd), mul_le_mul_of_nonneg_left h2 hA.le]
  · have hpos : 0 < A * D + m * d := by have := mul_pos hA hD; have := mul_nonneg hm hd; linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have h3' : a + m * (d * s) ≤ D * M := by rw [div_le_iff₀ hD] at h3; linarith [mul_comm M D]
    have i1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hm hd)
    have i2 := mul_le_mul_of_nonneg_left h3' hA.le
    nlinarith

/-- Lemma 7.1 for one word: under `Hyp`, for a nonempty word w over the levels, b ≥ 0 and
0 ≤ s ≤ a, ψ_T(b, a) ≤ V_w(max(b, a − s), a, d·s). -/
theorem conv_word (H : Hyp c d θ₀ lv) {w : List (ℝ × ℝ)} (hw : Wd θ₀ lv w) (hne : w ≠ [])
    {b a s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s) (hsa : s ≤ a) :
    psT c θ₀ lv b a ≤ V c w (max b (a - s)) a (d * s) := by
  have HB := H.toBase
  obtain ⟨p, w', rfl⟩ : ∃ p w', w = p :: w' := by
    cases w with | nil => exact absurd rfl hne | cons p w' => exact ⟨p, w', rfl⟩
  obtain ⟨hp, hw'⟩ := wd_cons hw
  have ha : 0 ≤ a := le_trans hs hsa
  have hA := Ad_pos HB hw
  have hL := AL_nonneg HB _ hw
  have hD := Dw_pos HB _ hw
  set top := max b (a - s)
  have htop : 0 ≤ top := le_trans hb (le_max_left _ _)
  have hV1 : Ad c (p :: w') * top ≤ V c (p :: w') top a (d * s) := by
    simp only [Ad, V]
    rw [max_mul_of_nonneg _ _ htop]
    refine max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
    refine le_trans ?_ (le_max_left _ _)
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (mul_nonneg (th_pos HB hp).le (Ad_pos HB hw').le)
  have hV2 : AL c (p :: w') * d * s ≤ V c (p :: w') top a (d * s) := by
    simp only [AL, V]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_left _ _)
    rw [mul_assoc (p.2 * Ad c w')]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg (th_pos HB hp).le (Ad_pos HB hw').le)
  have hV3 : (a + ((p :: w').length : ℝ) * (d * s)) / Dw c (p :: w') ≤ V c (p :: w') top a (d * s) := by
    simp only [V]; exact le_trans (le_refl _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hQ := cross HB.d0 (p :: w').length hA hL hD ha (s := s)
  have hVQ : Qf d (Ad c (p :: w')) (AL c (p :: w')) (Dw c (p :: w')) (p :: w').length * a ≤
      V c (p :: w') top a (d * s) := by
    refine le_trans hQ (max_le ?_ (max_le hV2 hV3))
    exact le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hA.le) hV1
  have hVb : Ad c (p :: w') * b ≤ V c (p :: w') top a (d * s) :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hA.le) hV1
  have hconv := H.conv _ hw hne b a hb ha
  refine le_trans (min_le_right _ _) (max_le ?_ (le_trans hconv (max_le hVb hVQ)))
  have : c ≤ Ad c (p :: w') := le_trans (kap_ge c p) (le_max_left _ _)
  exact le_trans (mul_le_mul_of_nonneg_right this hb) hVb

/-- Lemma 7.1 does not lower the level value: under `Hyp`, for b ≥ 0 and 0 ≤ s ≤ a,
ψ_T(b, a) ≤ ψ_S(max(b, a − s), a, d·s). -/
theorem conv_ineq (H : Hyp c d θ₀ lv) {b a s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s) (hsa : s ≤ a) :
    psT c θ₀ lv b a ≤ psS c θ₀ lv (max b (a - s)) a (d * s) := by
  have HB := H.toBase
  apply le_psS
  intro w
  refine le_trans ?_ (le_max_right _ _)
  by_cases hne : w.1 = []
  · rw [hne]; simp only [V]
    exact le_trans (min_le_left _ _) (max_le (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _))
  · exact conv_word H w.2 hne hb hs hsa

theorem nonneg_up (H : Base c d θ₀ lv) : ∀ (l : List ℝ), (∀ y ∈ l, 0 ≤ y) → ∀ y, 0 ≤ y → 0 ≤ up c θ₀ lv l y
  | [], _, y, _ => by simp only [up]; exact mul_nonneg (c0 H).le (le_max_left _ _)
  | b' :: r, hl, y, _ => by
      simp only [up]
      have hb'0 : 0 ≤ b' := hl b' (by simp)
      exact nonneg_up H r (fun z hz => hl z (by simp [hz])) _ (le_trans hb'0 (psT_ge H hb'0))

theorem Phi_nonneg (H : Base c d θ₀ lv) {L : RLine} (hL : NN L) : 0 ≤ Phi c θ₀ lv L := by
  obtain ⟨hb, hk⟩ := hL
  rcases L with ⟨bl, k⟩
  cases bl with
  | nil => cases k with
    | T a => simpa [Phi, KNN] using hk
    | S a e => simp [Phi]
  | cons b rest =>
    simp only [Phi]
    have hb0 : 0 ≤ b := hb b (by simp)
    exact nonneg_up H rest (fun y hy => hb y (by simp [hy])) _ (le_trans hb0 (pot_ge H k hb0))

/-- Under `Hyp`, for a ≥ 0 and the parameters of a `convN` step from `([], T a)`
(0 ≤ s ≤ a, max(0, a − s) ≤ g', a ≤ a₂, d·s ≤ e): a ≤ c·max(0, ψ_S(g', a₂, e)). -/
theorem first_ineq (H : Hyp c d θ₀ lv) {a s g' a₂ e : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hsa : s ≤ a)
    (hg : max 0 (a - s) ≤ g') (ha₂ : a ≤ a₂) (he : d * s ≤ e) :
    a ≤ c * max 0 (psS c θ₀ lv g' a₂ e) := by
  have HB := H.toBase
  have hc := c0 HB
  have h1 := conv_ineq H (le_refl 0) hs hsa
  have h2 : psS c θ₀ lv (max 0 (a - s)) a (d * s) ≤ psS c θ₀ lv g' a₂ e := psS_mono HB hg ha₂ he
  have h3 : a ≤ c * psT c θ₀ lv 0 a := by
    have hT := Tm_ge HB (le_refl 0) ha
    unfold psT
    rw [max_eq_right ha, mul_zero, max_eq_right (le_trans (div_nonneg ha hc.le) hT)]
    rcases le_total a (Tm c θ₀ lv 0 a) with h | h
    · rw [min_eq_left h]; nlinarith [HB.c1]
    · rw [min_eq_right h]
      have : c * (a / c) = a := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hT hc.le]
  calc a ≤ c * psT c θ₀ lv 0 a := h3
    _ ≤ c * psS c θ₀ lv g' a₂ e := mul_le_mul_of_nonneg_left (le_trans h1 h2) hc.le
    _ ≤ c * max 0 (psS c θ₀ lv g' a₂ e) := mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le

/-- Under `Hyp c d θ₀ lv`, an `RStep c d` from a line with nonnegative entries does not lower `Phi`. -/
theorem phi_step (H : Hyp c d θ₀ lv) {L L' : RLine} (h : RStep c d L L') (hL : NN L) :
    Phi c θ₀ lv L ≤ Phi c θ₀ lv L' := by
  have HB := H.toBase
  have hc0 : 0 ≤ c := (c0 HB).le
  have hL' := nn_step hc0 HB.d0 h hL
  obtain ⟨hb, hk⟩ := hL
  cases h with
  | convM b rest a s b₁ a₂ e hs hsa h₁ ha he =>
    simp only [Phi, pot]
    apply up_mono HB
    have hb0 : 0 ≤ b := hb b (by simp)
    exact le_trans (conv_ineq H hb0 hs hsa) (psS_mono HB h₁ ha he)
  | convN bl a s g' a₂ e hs hsa hg ha he =>
    simp only [KNN] at hk
    cases bl with
    | nil =>
      simp only [Phi, pot, up]
      exact first_ineq H hk hs hsa (by simpa [pin] using hg) ha he
    | cons b rest =>
      simp only [Phi, pot, up]
      apply up_mono HB
      have hb0 : 0 ≤ b := hb b (by simp)
      have hg' : max b (a - s) ≤ g' := by simpa [pin] using hg
      have hY := le_trans (conv_ineq H hb0 hs hsa) (psS_mono HB hg' ha he)
      have hbY : b ≤ psS c θ₀ lv g' a₂ e :=
        le_trans (le_trans (le_max_left _ _) hg') (psS_ge HB (le_trans hb0 (le_trans (le_max_left _ _) hg')))
      exact le_trans hY (push_ineq HB hb0 hbY)
  | speedM b rest a e x b' L a₂ e₂ hx hex h' hL ha he =>
    simp only [KNN] at hk
    simp only [Phi, pot, up]
    apply up_mono HB
    have hb0 : 0 ≤ b := hb b (by simp)
    refine le_trans (speed_ineq HB hb0 hx) (psT_mono HB h' ?_)
    exact mul_le_mul_of_nonneg_left (max_le_max h' (psS_mono HB hL ha he)) hc0
  | speedN bl a e x g₁ g₂ a₂ e₂ hx hex h₁ h₂ ha he =>
    simp only [KNN] at hk
    cases bl with
    | nil =>
      simp only [Phi]
      exact Phi_nonneg HB hL'
    | cons b rest =>
      simp only [Phi, pot, up]
      apply up_mono HB
      have hb0 : 0 ≤ b := hb b (by simp)
      have h₁' : max b (x + e) ≤ g₁ := by simpa [pin] using h₁
      have h₂' : max b e ≤ g₂ := by simpa [pin] using h₂
      have hS := le_trans (speed_ineq HB hb0 hx) (psT_mono HB h₁'
        (mul_le_mul_of_nonneg_left (max_le_max h₁' (psS_mono HB h₂' ha he)) hc0))
      have hg₁0 : 0 ≤ g₁ := le_trans (le_trans hb0 (le_max_left _ _)) h₁'
      have hbY : b ≤ psT c θ₀ lv g₁ (c * max g₁ (psS c θ₀ lv g₂ a₂ e₂)) :=
        le_trans (le_trans (le_max_left _ _) h₁') (psT_ge HB hg₁0)
      exact le_trans hS (push_ineq HB hb0 hbY)
  | slow b rest k a' hh =>
    have hb0 : 0 ≤ b := hb b (by simp)
    cases rest with
    | nil =>
      simp only [Phi, up, pin] at hh ⊢
      calc c * max 0 (pot c θ₀ lv b k) ≤ c * max (max 0 b) k.time := by
            apply mul_le_mul_of_nonneg_left _ hc0
            rw [max_assoc]; exact max_le_max le_rfl (pot_le HB b k hb0)
        _ ≤ a' := hh
    | cons b' rest' =>
      simp only [Phi, up, pin, pot] at hh ⊢
      apply up_mono HB
      apply psT_mono HB le_rfl
      calc c * max b' (pot c θ₀ lv b k) ≤ c * max (max b' b) k.time := by
            apply mul_le_mul_of_nonneg_left _ hc0
            rw [max_assoc]; exact max_le_max le_rfl (pot_le HB b k hb0)
        _ ≤ a' := hh

/-- Under `Hyp c d θ₀ lv`: along an `RPath c d M n` from `M 0 = ([], T a₀)` with a₀ ≥ 0 to
`M n = ([], T a')`, a₀ ≤ a'. -/
theorem qf_ge (H : Hyp c d θ₀ lv) {M : ℕ → RLine} {n : ℕ} (hp : RPath c d M n) {a₀ a' : ℝ}
    (ha₀ : 0 ≤ a₀) (h0 : M 0 = ([], .T a₀)) (hN : M n = ([], .T a')) : a₀ ≤ a' := by
  have HB := H.toBase
  have hc0 : 0 ≤ c := (c0 HB).le
  have hnn : ∀ i ≤ n, NN (M i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ⟨by simp, by simpa [KNN] using ha₀⟩
    | succ j ih => intro hj; exact nn_step hc0 HB.d0 (hp j (by omega)) (ih (by omega))
  have hmono : ∀ i ≤ n, Phi c θ₀ lv (M 0) ≤ Phi c θ₀ lv (M i) := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ j ih => intro hj; exact le_trans (ih (by omega)) (phi_step H (hp j (by omega)) (hnn j (by omega)))
  have := hmono n le_rfl
  rw [h0, hN] at this
  simpa [Phi] using this

/-- Under `Hyp c d θ₀ lv` there is no strict normal-form proof `HY.NF c d M n`. -/
theorem no_nf (H : Hyp c d θ₀ lv) (M : ℕ → HY.Line) (n : ℕ) : ¬ HY.NF c d M n := by
  have HB := H.toBase
  rintro ⟨hn, hp, ⟨a₀, h0⟩, ⟨a', hN⟩, _, h1, hlt, _⟩
  have hrp : RPath c d (fun i => enc (M i)) n := fun i hi => sim (c0 HB).le (hp i hi)
  have hT0 : (M 0).2.time = a₀ := by rw [h0]; rfl
  have hTn : (M n).2.time = a' := by rw [hN]; rfl
  have ha₀ : 0 ≤ a₀ := by rw [← hT0]; linarith
  have := qf_ge H hrp ha₀ (by show enc (M 0) = _; rw [h0]; rfl) (by show enc (M n) = _; rw [hN]; rfl)
  rw [hT0, hTn] at hlt
  linarith

theorem Tm_gt (H : Base c d θ₀ lv) (ht : ∀ p ∈ (0, θ₀) :: lv, 1 < p.2) {b a : ℝ} (_hb : 0 ≤ b) (ha : 0 < a) :
    ∃ k > 1, k * a / c ≤ Tm c θ₀ lv b a := by
  have hc := c0 H
  let ths := ((0, θ₀) :: lv).map Prod.snd
  have hne : ths ≠ [] := by simp [ths]
  let k := ths.foldr min θ₀
  have hk1 : 1 < k := by
    have : ∀ l : List (ℝ × ℝ), (∀ p ∈ l, 1 < p.2) → 1 < (l.map Prod.snd).foldr min θ₀ := by
      intro l hl
      induction l with
      | nil => simpa using ht (0, θ₀) (by simp)
      | cons q r ih => simp only [List.map_cons, List.foldr_cons]; exact lt_min (hl q (by simp)) (ih (fun p hp => hl p (by simp [hp])))
    exact this _ ht
  have hkle : ∀ p ∈ (0, θ₀) :: lv, k ≤ p.2 := by
    have : ∀ l : List (ℝ × ℝ), ∀ p ∈ l, (l.map Prod.snd).foldr min θ₀ ≤ p.2 := by
      intro l
      induction l with
      | nil => intro p hp; simp at hp
      | cons q r ih =>
        intro p hp
        simp only [List.map_cons, List.foldr_cons]
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact min_le_left _ _
        · exact le_trans (min_le_right _ _) (ih p hp)
    exact this _
  refine ⟨k, hk1, le_Tm ?_ ?_⟩
  · rw [div_mul_eq_mul_div, mul_comm θ₀ a]
    exact div_le_div_of_nonneg_right (by nlinarith [hkle (0, θ₀) (by simp)]) hc.le
  · intro p hp
    refine le_trans ?_ (le_max_right _ _)
    rw [div_mul_eq_mul_div, mul_comm p.2 a]
    exact div_le_div_of_nonneg_right (by nlinarith [hkle p (by simp [hp])]) hc.le

/-- Under `Hyp`, if every θ (level 0 included) is > 1 and c > 1: for a > 0 and the parameters
of a `convN` step from `([], T a)` (0 ≤ s ≤ a, max(0, a − s) ≤ g', a ≤ a₂, d·s ≤ e),
a < c·max(0, ψ_S(g', a₂, e)). -/
theorem first_strict (H : Hyp c d θ₀ lv) (ht : ∀ p ∈ (0, θ₀) :: lv, 1 < p.2) (hc1 : 1 < c)
    {a s g' a₂ e : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hsa : s ≤ a) (hg : max 0 (a - s) ≤ g') (ha₂ : a ≤ a₂)
    (he : d * s ≤ e) : a < c * max 0 (psS c θ₀ lv g' a₂ e) := by
  have HB := H.toBase
  have hc := c0 HB
  have h1 := conv_ineq H (le_refl 0) hs hsa
  have h2 : psS c θ₀ lv (max 0 (a - s)) a (d * s) ≤ psS c θ₀ lv g' a₂ e := psS_mono HB hg ha₂ he
  have h3 : a < c * psT c θ₀ lv 0 a := by
    obtain ⟨k, hk, hT⟩ := Tm_gt HB ht (le_refl 0) ha
    have hT0 : 0 ≤ Tm c θ₀ lv 0 a := le_trans (by positivity) hT
    unfold psT
    rw [max_eq_right ha.le, mul_zero, max_eq_right hT0]
    rcases le_total a (Tm c θ₀ lv 0 a) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]
      have : c * (k * a / c) = k * a := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hT hc.le]
  calc a < c * psT c θ₀ lv 0 a := h3
    _ ≤ c * psS c θ₀ lv g' a₂ e := mul_le_mul_of_nonneg_left (le_trans h1 h2) hc.le
    _ ≤ c * max 0 (psS c θ₀ lv g' a₂ e) := mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le

/-- Under `Hyp c d θ₀ lv`, with every θ > 1 and c > 1: along an `RPath c d M n` with n ≥ 1 from
`M 0 = ([], T a₀)`, a₀ > 0, to `M n = ([], T a')`, a₀ < a'. -/
theorem qf_gt (H : Hyp c d θ₀ lv) (ht : ∀ p ∈ (0, θ₀) :: lv, 1 < p.2) (hc : 1 < c) {M : ℕ → RLine}
    {n : ℕ} (hp : RPath c d M n) (hn : 1 ≤ n) {a₀ a' : ℝ} (ha₀ : 0 < a₀) (h0 : M 0 = ([], .T a₀))
    (hN : M n = ([], .T a')) : a₀ < a' := by
  have HB := H.toBase
  have hc0 : 0 ≤ c := (c0 HB).le
  have hnn : ∀ i ≤ n, NN (M i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ⟨by simp, by simpa [KNN] using ha₀.le⟩
    | succ j ih => intro hj; exact nn_step hc0 HB.d0 (hp j (by omega)) (ih (by omega))
  have hmono : ∀ i, 1 ≤ i → i ≤ n → Phi c θ₀ lv (M 1) ≤ Phi c θ₀ lv (M i) := by
    intro i h1 hi
    induction i with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; exact le_rfl
      · exact le_trans (ih hj (by omega)) (phi_step H (hp j (by omega)) (hnn j (by omega)))
  have hfirst : a₀ < Phi c θ₀ lv (M 1) := by
    have h01 := hp 0 (by omega)
    rw [h0] at h01
    generalize hM1 : M 1 = L1 at h01
    cases h01 with
    | convN bl a s g' a₂ e hs hsa hg ha he =>
      simp only [Phi, pot, up]
      exact first_strict H ht hc ha₀ hs hsa (by simpa [pin] using hg) ha he
  have := lt_of_lt_of_le hfirst (hmono n hn le_rfl)
  rw [hN] at this
  simpa [Phi] using this

/-- Under `Hyp c d θ₀ lv`, with every θ > 1 and c > 1: along a `HY.Step c d` path of length
n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')`, a₀ < a'. -/
theorem no_nf_le (H : Hyp c d θ₀ lv) (ht : ∀ p ∈ (0, θ₀) :: lv, 1 < p.2) (hc : 1 < c) (M : ℕ → HY.Line)
    (n : ℕ) (hn : 1 ≤ n) (hp : HY.Path (HY.Step c d) M n) {a₀ a' : ℝ} (ha₀ : 0 < a₀)
    (h0 : M 0 = ([], .T a₀)) (hN : M n = ([], .T a')) : a₀ < a' := by
  have HB := H.toBase
  have hrp : RPath c d (fun i => enc (M i)) n := fun i hi => sim (c0 HB).le (hp i hi)
  exact qf_gt H ht hc hrp hn ha₀ (by show enc (M 0) = _; rw [h0]; rfl) (by show enc (M n) = _; rw [hN]; rfl)

end lemmas

end

/-- For c₀ ≤ c, an `RStep c d L L'` from a line `L` with nonnegative entries is an
`RStep c₀ d L L'`. -/
theorem rstep_mono {c₀ c d : ℝ} (hc : c₀ ≤ c) {L L' : RLine} (hL : NN L) (h : RStep c d L L') :
    RStep c₀ d L L' := by
  cases h with
  | convM b rest a s b₁ a₂ e hs hsa h₁ ha he => exact .convM b rest a s b₁ a₂ e hs hsa h₁ ha he
  | convN bl a s g a₂ e hs hsa hg ha he => exact .convN bl a s g a₂ e hs hsa hg ha he
  | speedM b rest a e x b' L a₂ e₂ hx hex h' hL' ha he => exact .speedM b rest a e x b' L a₂ e₂ hx hex h' hL' ha he
  | speedN bl a e x g₁ g₂ a₂ e₂ hx hex h₁ h₂ ha he => exact .speedN bl a e x g₁ g₂ a₂ e₂ hx hex h₁ h₂ ha he
  | slow b rest k a' hh =>
    refine .slow b rest k a' (le_trans ?_ hh)
    have hb : 0 ≤ b := hL.1 b (by simp)
    have : 0 ≤ max (max (pin rest) b) k.time := le_trans hb (le_trans (le_max_right _ _) (le_max_left _ _))
    exact mul_le_mul_of_nonneg_right hc this

/-- For 0 ≤ c₀ ≤ c and d ≥ 0, an `RPath c d M n` from `([], T a₀)` with a₀ ≥ 0 is an
`RPath c₀ d M n`. -/
theorem rpath_mono {c₀ c d : ℝ} (hc0 : 0 ≤ c₀) (hc : c₀ ≤ c) (hd : 0 ≤ d) {M : ℕ → RLine} {n : ℕ}
    (hp : RPath c d M n) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (h0 : M 0 = ([], .T a₀)) : RPath c₀ d M n := by
  have hnn : ∀ i ≤ n, NN (M i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ⟨by simp, by simpa [KNN] using ha₀⟩
    | succ j ih => intro hj; exact nn_step (le_trans hc0 hc) hd (hp j (by omega)) (ih (by omega))
  exact fun i hi => rstep_mono hc (hnn i hi.le) (hp i hi)

/-- If `Hyp c₀ d θ₀ lv` and c₀ ≤ c: along an `RPath c d M n` from `([], T a₀)`, a₀ ≥ 0, to
`([], T a')`, a₀ ≤ a'. -/
theorem rge_of {c₀ d θ₀ : ℝ} {lv : List (ℝ × ℝ)} (H : Hyp c₀ d θ₀ lv) {c : ℝ} (hc : c₀ ≤ c)
    {M : ℕ → RLine} {n : ℕ} (hp : RPath c d M n) {a₀ a' : ℝ} (ha₀ : 0 ≤ a₀) (h0 : M 0 = ([], .T a₀))
    (hN : M n = ([], .T a')) : a₀ ≤ a' :=
  qf_ge H (rpath_mono (c0 H.toBase).le hc H.d0 hp ha₀ h0) ha₀ h0 hN

/-- If `Hyp c₀ d θ₀ lv`, every θ > 1, 1 < c₀ and c₀ ≤ c: along an `RPath c d M n` with n ≥ 1 from
`([], T a₀)`, a₀ > 0, to `([], T a')`, a₀ < a'. -/
theorem rgt_of {c₀ d θ₀ : ℝ} {lv : List (ℝ × ℝ)} (H : Hyp c₀ d θ₀ lv) (ht : ∀ p ∈ (0, θ₀) :: lv, 1 < p.2)
    (hc1 : 1 < c₀) {c : ℝ} (hc : c₀ ≤ c) {M : ℕ → RLine} {n : ℕ} (hp : RPath c d M n) (hn : 1 ≤ n)
    {a₀ a' : ℝ} (ha₀ : 0 < a₀) (h0 : M 0 = ([], .T a₀)) (hN : M n = ([], .T a')) : a₀ < a' :=
  qf_gt H ht hc1 (rpath_mono (c0 H.toBase).le hc H.d0 hp ha₀.le h0) hn ha₀ h0 hN

/-- If `Hyp c₀ d θ₀ lv` and c₀ ≤ c, there is no strict normal-form proof `HY.NF c d M n`. -/
theorem no_nf_of {c₀ d θ₀ : ℝ} {lv : List (ℝ × ℝ)} (H : Hyp c₀ d θ₀ lv) {c : ℝ} (hc : c₀ ≤ c)
    (M : ℕ → HY.Line) (n : ℕ) : ¬ HY.NF c d M n := by
  rintro ⟨hn, hp, ⟨a₀, h0⟩, ⟨a', hN⟩, _, h1, hlt, _⟩
  have hc0 : 0 ≤ c := le_trans (c0 H.toBase).le hc
  have hrp : RPath c d (fun i => enc (M i)) n := fun i hi => sim hc0 (hp i hi)
  have hT0 : (M 0).2.time = a₀ := by rw [h0]; rfl
  have hTn : (M n).2.time = a' := by rw [hN]; rfl
  have ha₀ : 0 ≤ a₀ := by rw [← hT0]; linarith
  have := rge_of H hc hrp ha₀ (by show enc (M 0) = _; rw [h0]; rfl) (by show enc (M n) = _; rw [hN]; rfl)
  rw [hT0, hTn] at hlt
  linarith

/-- If `Hyp c₀ d θ₀ lv`, every θ > 1, 1 < c₀ and c₀ ≤ c: along a `HY.Step c d` path of length
n ≥ 1 from `([], T a₀)`, a₀ > 0, to `([], T a')`, a₀ < a'. -/
theorem no_nf_le_of {c₀ d θ₀ : ℝ} {lv : List (ℝ × ℝ)} (H : Hyp c₀ d θ₀ lv)
    (ht : ∀ p ∈ (0, θ₀) :: lv, 1 < p.2) (hc1 : 1 < c₀) {c : ℝ} (hc : c₀ ≤ c) (M : ℕ → HY.Line) (n : ℕ)
    (hn : 1 ≤ n) (hp : HY.Path (HY.Step c d) M n) {a₀ a' : ℝ} (ha₀ : 0 < a₀) (h0 : M 0 = ([], .T a₀))
    (hN : M n = ([], .T a')) : a₀ < a' := by
  have hrp : RPath c d (fun i => enc (M i)) n := fun i hi => sim (by linarith) (hp i hi)
  exact rgt_of H ht hc1 hc hrp hn ha₀ (by show enc (M 0) = _; rw [h0]; rfl) (by show enc (M n) = _; rw [hN]; rfl)

end HLM
end PastaMath.OneTapeThreshold
