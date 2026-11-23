-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The relaxed MA-versus-BPTS calculus and its limit

The alternation-trading calculus of A. S. Mudigonda and R. Williams, "Time-space lower bounds for
simulating proof systems with quantum and randomized verifiers" (ITCS 2021; arXiv 2012.00330,
whose numbering is used here: Definition 2.14 rules 2–5, Theorem 2.10, Corollaries 2.8 and 2.11,
Lemmas 5.1 and 5.2), for ∃·BPTIME[n] versus BPTS, in a relaxed homogeneous form.

Hypothesis: ∃·BPTIME[n] ⊆ BPTS[n^c]. A line `(bs, k, a)` lists the output superscripts of its blocks
innermost first (guess exponents are dropped: every line of such a proof is orderly, Lemma 2.17),
`k = true` for a BPTS kernel and `false` for a TS kernel, and `a` is the kernel exponent.
The input superscript in front of the outermost block is 0 (the paper has 1; 0 is more permissive).

The source rules, with the paper's exact outputs:
* Theorem 2.10 (rule 3): BPTS[n^a] ⊆ (∃ n^0)^1 (∀ n^x)^{max(x,1)} (∃ x log n) TS[n^{a−x}];
* Corollary 2.11 (rule 4): ⋯(Q n^{a_k})^{b} BPTS[n^a] ⊆
  ⋯(Q n^{a_k})^{b} (Q' n^x)^{max(b,x)} (Q x log n)^{b} TS[n^{a−x}];
* Corollary 2.8 (rule 2): ⋯(Q n^{a_k})^{b} TS[n^a] ⊆
  ⋯(Q n^{max(a_k,x)})^{max(b,x)} (Q' x log n)^{b} TS[n^{a−x}];
* Lemma 5.1 (rule 5, α = 1): ⋯^{b'} (Q n^{a_k})^{b} K[n^a] ⊆ ⋯^{b'} BPTS[n^{c·max(a, b, a_k, b')}].
`MStep` relaxes them: every speedup needs 0 ≤ x ≤ a and gives a new kernel exponent a₂ ≥ a − x, and
the new outputs are only bounded below; the slowdown has no parameter x.
* `rspeed0`, from a quantifier-free line of either kernel: new outputs b₁ ≥ 0, b₂ ≥ max(x, 0),
  b₃ ≥ 0 (outermost first), TS kernel;
* `rspeed`, on either kernel (TS ⊆ BPTS): the innermost output b is kept, new outputs
  b₂ ≥ max(b, x) and b₃ ≥ b, TS kernel;
* `dspeed`, on a TS kernel: b is replaced by t₂ ≥ max(b, x), a new output b₃ ≥ b, TS kernel;
* `slow`, on either kernel: the innermost block is removed and the BPTS kernel is any e ≥
  c·max(b', b, a), where b' is the output of the next block, or 0 if there is none.

`UStep` adds the unmerged orientation of the randomized speedup (three new blocks), and `StepW`
adds weakening of an existing line (`Weaker`: the same number of blocks, superscripts and the
kernel exponent raised, the kernel kept or replaced by BPTS). `XStep` adds two rules that are
needed when the entries are read as maximal runs of adjacent same-type blocks (`rspeedS`,
`slowIn`); under that reading combining or splitting blocks is a weakening (see `MWL.StepX` and
`MWL.lit_x`).

Main results: let c > 0 and c² ≥ c + 1 (that is, c ≥ φ). For a₀ ≥ 0, every quantifier-free line
BPTS[n^{a'}] reached from BPTS[n^{a₀}] has a' ≥ c·a₀ if the path has at least one `MStep` or
`UStep` step (`qf_ge`, `qf_ge_u`), contains at least one rule step (`StepW`, `qf_ge_w`), or passes
through a line with a block (`XStep`, `qf_ge_x`). So there is no refutation from a₀ > 0, strict or
not (`no_mrefutation`, `no_urefutation`, `no_wrefutation`, `no_xrefutation`, with the rule-step and
block conditions of `WRefutes` and `XRefutes`). The proof is a potential `Φ c g` with
g = 1/(c² − 1): for any g with `Facts c g`, it does not decrease along a step from a line with
nonnegative entries (`phi_step`, `phi_ustep`, `phi_xstep`) or under a weakening of such a line
(`phi_mono`).
-/

namespace PastaMath.MWThreshold
namespace MW

abbrev MLine := List ℝ × Bool × ℝ

def pin : List ℝ → ℝ
  | [] => 0
  | b :: _ => b

inductive MStep (c : ℝ) : MLine → MLine → Prop
  | rspeed0 (k : Bool) (a x b₁ b₂ b₃ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a) (h₁ : 0 ≤ b₁)
      (h₂ : x ≤ b₂) (h₂' : 0 ≤ b₂) (h₃ : 0 ≤ b₃) (ha : a - x ≤ a₂) :
      MStep c ([], k, a) ([b₃, b₂, b₁], false, a₂)
  | rspeed (b : ℝ) (rest : List ℝ) (k : Bool) (a x b₂ b₃ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₂ : max b x ≤ b₂) (h₃ : b ≤ b₃) (ha : a - x ≤ a₂) :
      MStep c (b :: rest, k, a) (b₃ :: b₂ :: b :: rest, false, a₂)
  | dspeed (b : ℝ) (rest : List ℝ) (a x t₂ b₃ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₂ : max b x ≤ t₂) (h₃ : b ≤ b₃) (ha : a - x ≤ a₂) :
      MStep c (b :: rest, false, a) (b₃ :: t₂ :: rest, false, a₂)
  | slow (b : ℝ) (rest : List ℝ) (k : Bool) (a e : ℝ) (he : c * max (max (pin rest) b) a ≤ e) :
      MStep c (b :: rest, k, a) (rest, true, e)

def Path (c : ℝ) (M : ℕ → MLine) (n : ℕ) : Prop := ∀ i < n, MStep c (M i) (M (i + 1))

/-- A refutation (MW21 Def. 2.14 / Lemma 5.2), non-strict: an `MStep` path
BPTS[n^{a₀}] ⊆ … ⊆ BPTS[n^{a'}] with a₀ > 0, a' ≤ a₀ and at least one step. Intermediate lines are
unrestricted (this only strengthens the theorem). -/
def MRefutes (c : ℝ) (n : ℕ) (M : ℕ → MLine) : Prop :=
  1 ≤ n ∧ Path c M n ∧ ∃ a₀ a', 0 < a₀ ∧ M 0 = ([], true, a₀) ∧ M n = ([], true, a') ∧ a' ≤ a₀

def NN (L : MLine) : Prop := (∀ b ∈ L.1, 0 ≤ b) ∧ 0 ≤ L.2.2

/-- Line potential: max(b, a) on BPTS lines, max(b, g·a) on TS lines. -/
def pot (g b : ℝ) (k : Bool) (a : ℝ) : ℝ := if k then max b a else max b (g * a)

/-- Lift through the outer blocks: popping a block of superscript b' costs c·max(b', ·), and the
last lift, for the input, costs c·max(0, ·). -/
def up (c : ℝ) : List ℝ → ℝ → ℝ
  | [], y => c * max 0 y
  | b :: rest, y => up c rest (c * max b y)

def Φ (c g : ℝ) : MLine → ℝ
  | ([], _, a) => a
  | (b :: rest, k, a) => up c rest (pot g b k a)

theorem up_mono {c : ℝ} (hc : 0 ≤ c) : ∀ (l : List ℝ) {y y' : ℝ}, y ≤ y' → up c l y ≤ up c l y'
  | [], y, y', h => by
      simp only [up]
      exact mul_le_mul_of_nonneg_left (max_le_max le_rfl h) hc
  | b :: rest, y, y', h => by
      simp only [up]
      exact up_mono hc rest (mul_le_mul_of_nonneg_left (max_le_max le_rfl h) hc)

/-- The balance inequality: for g ≥ 0 (and any x, a), (1+g)·max(x, g(a−x)) ≥ g·a. -/
theorem bal {g a x : ℝ} (hg : 0 ≤ g) :
    g * a ≤ (1 + g) * max x (g * (a - x)) := by
  have h1 : x ≤ max x (g * (a - x)) := le_max_left _ _
  have h2 : g * (a - x) ≤ max x (g * (a - x)) := le_max_right _ _
  nlinarith

/-- The inequalities on c and g used by the potential argument. -/
structure Facts (c g : ℝ) : Prop where
  c1 : 1 ≤ c
  g0 : 0 ≤ g
  g1 : g ≤ 1
  cg : 1 + g ≤ c
  c2g : 1 + g ≤ c ^ 2 * g

/-- For c > 0 with c² ≥ c + 1, g = 1/(c² − 1) satisfies `Facts`: 1 ≤ c, 0 ≤ g ≤ 1, 1 + g ≤ c and
1 + g ≤ c²·g (the last holds with equality, but only the inequality is recorded). -/
theorem facts_of_phi {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) : Facts c (1 / (c ^ 2 - 1)) := by
  have hc1 : 1 ≤ c := by nlinarith
  have hd : 0 < c ^ 2 - 1 := by nlinarith
  have hd2 : 1 ≤ c ^ 2 - 1 := by nlinarith
  refine ⟨hc1, by positivity, ?_, ?_, ?_⟩
  · rw [div_le_one hd]; linarith
  · rw [← sub_nonneg]
    have : c - (1 + 1 / (c ^ 2 - 1)) = ((c - 1) * (c ^ 2 - 1) - 1) / (c ^ 2 - 1) := by
      field_simp; ring
    rw [this]; apply div_nonneg _ hd.le; nlinarith
  · have : c ^ 2 * (1 / (c ^ 2 - 1)) = 1 + 1 / (c ^ 2 - 1) := by field_simp; ring
    rw [this]

/-- TS-speedup key inequality: for `Facts c g` and x ≥ 0 (any a), g·a ≤ c·max(x, g(a−x)). -/
theorem key_d {c g a x : ℝ} (F : Facts c g) (hx : 0 ≤ x) :
    g * a ≤ c * max x (g * (a - x)) := by
  have hb := bal (a := a) (x := x) F.g0
  have hm : 0 ≤ max x (g * (a - x)) := le_trans hx (le_max_left _ _)
  have : (1 + g) * max x (g * (a - x)) ≤ c * max x (g * (a - x)) :=
    mul_le_mul_of_nonneg_right F.cg hm
  linarith

/-- BPTS-speedup key inequality: for `Facts c g` and 0 ≤ x ≤ a, a ≤ c²·max(x, g(a−x)). -/
theorem key_r {c g a x : ℝ} (F : Facts c g) (hx : 0 ≤ x) (hxa : x ≤ a) :
    a ≤ c ^ 2 * max x (g * (a - x)) := by
  have hb := bal (a := a) (x := x) F.g0
  have hm : 0 ≤ max x (g * (a - x)) := le_trans hx (le_max_left _ _)
  have hg1 : 0 < 1 + g := by linarith [F.g0]
  have h1 : (1 + g) * a ≤ c ^ 2 * g * a := by
    have ha : 0 ≤ a := le_trans hx hxa
    nlinarith [F.c2g]
  have h2 : c ^ 2 * g * a ≤ c ^ 2 * ((1 + g) * max x (g * (a - x))) := by
    have : 0 ≤ c ^ 2 := by positivity
    nlinarith
  nlinarith

theorem pot_le {g b a : ℝ} (k : Bool) (hg1 : g ≤ 1) (ha : 0 ≤ a) :
    pot g b k a ≤ max b a := by
  cases k
  · simp only [pot, Bool.false_eq_true, if_false]
    exact max_le_max le_rfl (by nlinarith)
  · simp [pot]

theorem pot_ge_b {g b a : ℝ} (k : Bool) : b ≤ pot g b k a := by
  cases k <;> simp [pot]

theorem pot_d_ge {g b a : ℝ} : g * a ≤ pot g b false a := by simp [pot]

theorem pot_r_ge {g b a : ℝ} (k : Bool) (hg1 : g ≤ 1) (ha : 0 ≤ a) : g * a ≤ pot g b k a := by
  cases k
  · simp [pot]
  · simp only [pot, if_true]; exact le_trans (by nlinarith) (le_max_right _ _)

theorem nn_step {c : ℝ} (hc : 0 ≤ c) {L L' : MLine} (h : MStep c L L') (hL : NN L) : NN L' := by
  obtain ⟨hb, ha⟩ := hL
  cases h with
  | rspeed0 k a x b₁ b₂ b₃ a₂ hx hxa h₁ h₂ h₂' h₃ hA =>
    refine ⟨?_, by simp only at ha ⊢; linarith⟩
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  | rspeed b rest k a x b₂ b₃ a₂ hx hxa h₂ h₃ hA =>
    have hb0 : 0 ≤ b := hb b (by simp)
    refine ⟨?_, by simp only at ha ⊢; linarith⟩
    intro y hy; simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · linarith
    · exact le_trans (le_trans hb0 (le_max_left _ _)) h₂
    · exact hb y (by simp [hy])
  | dspeed b rest a x t₂ b₃ a₂ hx hxa h₂ h₃ hA =>
    have hb0 : 0 ≤ b := hb b (by simp)
    refine ⟨?_, by simp only at ha ⊢; linarith⟩
    intro y hy; simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · linarith
    · exact le_trans (le_trans hb0 (le_max_left _ _)) h₂
    · exact hb y (by simp [hy])
  | slow b rest k a e he =>
    refine ⟨fun y hy => hb y (by simp [hy]), ?_⟩
    simp only at ha ⊢
    have : 0 ≤ c * max (max (pin rest) b) a := mul_nonneg hc (le_trans ha (le_max_right _ _))
    linarith

/-- For g with `Facts c g` (`facts_of_phi` gives g = 1/(c² − 1) when c > 0 and c² ≥ c + 1),
`Φ c g` does not decrease along an `MStep` step from a line with nonnegative entries (`NN`). -/
theorem phi_step {c g : ℝ} (F : Facts c g) {L L' : MLine} (h : MStep c L L') (hL : NN L) :
    Φ c g L ≤ Φ c g L' := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  obtain ⟨hb, ha⟩ := hL
  cases h with
  | rspeed0 k a x b₁ b₂ b₃ a₂ hx hxa h₁ h₂ h₂' h₃ hA =>
    simp only at ha
    simp only [Φ, up]
    -- Φ L' = c·max(0, c·max(b₁, pot b₃ false a₂ lifted through b₂))
    have hp : g * (a - x) ≤ pot g b₃ false a₂ :=
      le_trans (mul_le_mul_of_nonneg_left hA F.g0) pot_d_ge
    have hy2 : c * max x (g * (a - x)) ≤ c * max b₂ (pot g b₃ false a₂) :=
      mul_le_mul_of_nonneg_left (max_le_max h₂ hp) hc0
    have hy1 : c * (c * max x (g * (a - x))) ≤ c * max b₁ (c * max b₂ (pot g b₃ false a₂)) :=
      mul_le_mul_of_nonneg_left (le_trans hy2 (le_max_right _ _)) hc0
    have hk := key_r F hx hxa
    have hY : a ≤ c * max b₁ (c * max b₂ (pot g b₃ false a₂)) := by
      calc a ≤ c * (c * max x (g * (a - x))) := by nlinarith
        _ ≤ _ := hy1
    have hY0 : 0 ≤ c * max b₁ (c * max b₂ (pot g b₃ false a₂)) := by linarith [ha]
    have hm : c * max b₁ (c * max b₂ (pot g b₃ false a₂)) ≤
        max 0 (c * max b₁ (c * max b₂ (pot g b₃ false a₂))) := le_max_right _ _
    nlinarith [F.c1]
  | rspeed b rest k a x b₂ b₃ a₂ hx hxa h₂ h₃ hA =>
    simp only at ha
    simp only [Φ, up]
    apply up_mono hc0
    have hb0 : 0 ≤ b := hb b (by simp)
    have hp : g * (a - x) ≤ pot g b₃ false a₂ :=
      le_trans (mul_le_mul_of_nonneg_left hA F.g0) pot_d_ge
    have hy2 : c * max x (g * (a - x)) ≤ c * max b₂ (pot g b₃ false a₂) :=
      mul_le_mul_of_nonneg_left (max_le_max (le_trans (le_max_right _ _) h₂) hp) hc0
    have hk := key_r F hx hxa
    refine le_trans (pot_le k F.g1 ha) (max_le ?_ ?_)
    · calc b ≤ c * b := by nlinarith [F.c1]
        _ ≤ c * max b (c * max b₂ (pot g b₃ false a₂)) :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hc0
    · calc a ≤ c * (c * max x (g * (a - x))) := by nlinarith
        _ ≤ c * max b (c * max b₂ (pot g b₃ false a₂)) :=
            mul_le_mul_of_nonneg_left (le_trans hy2 (le_max_right _ _)) hc0
  | dspeed b rest a x t₂ b₃ a₂ hx hxa h₂ h₃ hA =>
    simp only at ha
    simp only [Φ, up]
    apply up_mono hc0
    have hb0 : 0 ≤ b := hb b (by simp)
    have hp : g * (a - x) ≤ pot g b₃ false a₂ :=
      le_trans (mul_le_mul_of_nonneg_left hA F.g0) pot_d_ge
    have hpb : b ≤ pot g b₃ false a₂ := le_trans h₃ (pot_ge_b false)
    simp only [pot, Bool.false_eq_true, if_false]
    apply max_le
    · calc b ≤ c * b := by nlinarith [F.c1]
        _ ≤ c * max t₂ (max b₃ (g * a₂)) := by
            apply mul_le_mul_of_nonneg_left _ hc0
            exact le_trans (le_max_left _ _) (le_trans h₂ (le_max_left _ _))
    · calc g * a ≤ c * max x (g * (a - x)) := key_d F hx
        _ ≤ c * max t₂ (max b₃ (g * a₂)) := by
            apply mul_le_mul_of_nonneg_left _ hc0
            apply max_le_max (le_trans (le_max_right _ _) h₂)
            simp only [pot, Bool.false_eq_true, if_false] at hp
            exact hp
  | slow b rest k a e he =>
    simp only at ha
    have hpot := pot_le (b := b) k F.g1 ha
    cases rest with
    | nil =>
      simp only [Φ, up, pin] at he ⊢
      calc c * max 0 (pot g b k a) ≤ c * max (max 0 b) a := by
            apply mul_le_mul_of_nonneg_left _ hc0
            rw [max_assoc]; exact max_le_max le_rfl hpot
        _ ≤ e := he
    | cons b' rest' =>
      simp only [Φ, up, pin] at he ⊢
      apply up_mono hc0
      calc c * max b' (pot g b k a) ≤ c * max (max b' b) a := by
            apply mul_le_mul_of_nonneg_left _ hc0
            rw [max_assoc]; exact max_le_max le_rfl hpot
        _ ≤ e := he
        _ ≤ pot g b' true e := by simp [pot]

theorem phi_path {c g : ℝ} (F : Facts c g) {M : ℕ → MLine} {n : ℕ} (hp : Path c M n)
    (h0 : NN (M 0)) : ∀ i, 1 ≤ i → i ≤ n → Φ c g (M 1) ≤ Φ c g (M i) ∧ NN (M i) := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  have hnn : ∀ i ≤ n, NN (M i) := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ j ih => intro hj; exact nn_step hc0 (hp j (by omega)) (ih (by omega))
  intro i h1 hi
  induction i with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨le_rfl, hnn 1 hi⟩
    · obtain ⟨h, _⟩ := ih hj (by omega)
      exact ⟨le_trans h (phi_step F (hp j (by omega)) (hnn j (by omega))), hnn _ hi⟩

/-- For `Facts c g`, any `MStep` step from a quantifier-free line of kernel exponent a₀ (either
kernel) reaches a line of potential at least c·a₀. -/
theorem first_step {c g : ℝ} (F : Facts c g) {a₀ : ℝ} {k : Bool} {L : MLine}
    (h : MStep c ([], k, a₀) L) : c * a₀ ≤ Φ c g L := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  cases h with
  | rspeed0 k a x b₁ b₂ b₃ a₂ hx hxa h₁ h₂ h₂' h₃ hA =>
    simp only [Φ, up]
    have hp : g * (a₀ - x) ≤ pot g b₃ false a₂ :=
      le_trans (mul_le_mul_of_nonneg_left hA F.g0) pot_d_ge
    have hy2 : c * max x (g * (a₀ - x)) ≤ c * max b₂ (pot g b₃ false a₂) :=
      mul_le_mul_of_nonneg_left (max_le_max h₂ hp) hc0
    have hk := key_r F hx hxa
    have h1 : a₀ ≤ c * max b₁ (c * max b₂ (pot g b₃ false a₂)) := by
      calc a₀ ≤ c * (c * max x (g * (a₀ - x))) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_trans hy2 (le_max_right _ _)) hc0
    exact mul_le_mul_of_nonneg_left (le_trans h1 (le_max_right _ _)) hc0

/-- **Limit theorem.** Let c > 0 with c² ≥ c + 1 (c ≥ φ) and a₀ ≥ 0. In the relaxed calculus
`MStep`, every quantifier-free line BPTS[n^{a'}] reached from BPTS[n^{a₀}] in n ≥ 1 steps has
a' ≥ c·a₀. (`no_mrefutation` deduces that there is no `MRefutes` refutation, from a₀ > 0.) -/
theorem qf_ge {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) {M : ℕ → MLine} {n : ℕ}
    (hp : Path c M n) (hn : 1 ≤ n) {a₀ a' : ℝ} (ha₀ : 0 ≤ a₀) (h0 : M 0 = ([], true, a₀))
    (hN : M n = ([], true, a')) : c * a₀ ≤ a' := by
  have F := facts_of_phi hc0 hphi
  have hnn0 : NN (M 0) := by rw [h0]; exact ⟨by simp, ha₀⟩
  have h1 : MStep c ([], true, a₀) (M 1) := by rw [← h0]; exact hp 0 (by omega)
  have hf := first_step F h1
  obtain ⟨hmono, _⟩ := phi_path F hp hnn0 n hn le_rfl
  rw [hN] at hmono
  have e : Φ c (1 / (c ^ 2 - 1)) ([], true, a') = a' := rfl
  rw [e] at hmono
  linarith

/-- For c > 0 with c² ≥ c + 1 there is no `MRefutes` refutation (n ≥ 1 steps, a₀ > 0, a' ≤ a₀). -/
theorem no_mrefutation {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) (n : ℕ) (M : ℕ → MLine) :
    ¬ MRefutes c n M := by
  rintro ⟨hn, hp, a₀, a', ha₀, h0, hN, hle⟩
  have := qf_ge hc0 hphi hp hn ha₀.le h0 hN
  have hc1 : 1 < c := by nlinarith
  nlinarith


/-! ### The unmerged randomized speedup -/

/-- `MStep` plus the unmerged randomized speedup, on either kernel: ⋯(Q)^b K[n^a] ⊆ ⋯(Q)^b
(Q' n^0)^{b₁} (¬Q' n^x)^{b₂} (Q' x log n)^{b₃} TS[n^{a₂}] with 0 ≤ x ≤ a and only lower bounds
b₁ ≥ 0, b₂ ≥ max(b, x), b₃ ≥ b, a₂ ≥ a − x (b₁ ≥ 0 is weaker than the value b₁ = b of
`MWL.StepU.rspeedU`). -/
inductive UStep (c : ℝ) : MLine → MLine → Prop
  | base {L L' : MLine} : MStep c L L' → UStep c L L'
  | rspeedU (b : ℝ) (rest : List ℝ) (k : Bool) (a x b₁ b₂ b₃ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₁ : 0 ≤ b₁) (h₂ : max b x ≤ b₂) (h₃ : b ≤ b₃) (ha : a - x ≤ a₂) :
      UStep c (b :: rest, k, a) (b₃ :: b₂ :: b₁ :: b :: rest, false, a₂)

def UPath (c : ℝ) (M : ℕ → MLine) (n : ℕ) : Prop := ∀ i < n, UStep c (M i) (M (i + 1))

/-- A non-strict refutation in `UStep`: n ≥ 1 steps from BPTS[n^{a₀}], a₀ > 0, to BPTS[n^{a'}],
a' ≤ a₀. -/
def URefutes (c : ℝ) (n : ℕ) (M : ℕ → MLine) : Prop :=
  1 ≤ n ∧ UPath c M n ∧ ∃ a₀ a', 0 < a₀ ∧ M 0 = ([], true, a₀) ∧ M n = ([], true, a') ∧ a' ≤ a₀

theorem nn_ustep {c : ℝ} (hc : 0 ≤ c) {L L' : MLine} (h : UStep c L L') (hL : NN L) : NN L' := by
  cases h with
  | base h => exact nn_step hc h hL
  | rspeedU b rest k a x b₁ b₂ b₃ a₂ hx hxa h₁ h₂ h₃ hA =>
    obtain ⟨hb, ha⟩ := hL
    have hb0 : 0 ≤ b := hb b (by simp)
    refine ⟨?_, by simp only at ha ⊢; linarith⟩
    intro y hy; simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | rfl | rfl | hy
    · linarith
    · exact le_trans (le_trans hb0 (le_max_left _ _)) h₂
    · exact h₁
    · exact hb0
    · exact hb y (by simp [hy])

/-- For `Facts c g`, `Φ c g` does not decrease along a `UStep` step from a line with nonnegative
entries. -/
theorem phi_ustep {c g : ℝ} (F : Facts c g) {L L' : MLine} (h : UStep c L L') (hL : NN L) :
    Φ c g L ≤ Φ c g L' := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  cases h with
  | base h => exact phi_step F h hL
  | rspeedU b rest k a x b₁ b₂ b₃ a₂ hx hxa h₁ h₂ h₃ hA =>
    obtain ⟨hb, ha⟩ := hL
    simp only at ha
    simp only [Φ, up]
    apply up_mono hc0
    have hb0 : 0 ≤ b := hb b (by simp)
    have hp : g * (a - x) ≤ pot g b₃ false a₂ :=
      le_trans (mul_le_mul_of_nonneg_left hA F.g0) pot_d_ge
    have hY : c * max x (g * (a - x)) ≤ c * max b₂ (pot g b₃ false a₂) :=
      mul_le_mul_of_nonneg_left (max_le_max (le_trans (le_max_right _ _) h₂) hp) hc0
    have hk := key_r F hx hxa
    have hY0 : 0 ≤ c * max b₂ (pot g b₃ false a₂) :=
      le_trans (mul_nonneg hc0 (le_trans hx (le_max_left _ _))) hY
    set Y := c * max b₂ (pot g b₃ false a₂) with hYdef
    have hZ : c * Y ≤ c * max b₁ Y := mul_le_mul_of_nonneg_left (le_max_right _ _) hc0
    have hcY : Y ≤ c * Y := by nlinarith [F.c1]
    have haY : a ≤ c * Y := by
      calc a ≤ c ^ 2 * max x (g * (a - x)) := hk
        _ = c * (c * max x (g * (a - x))) := by ring
        _ ≤ c * Y := mul_le_mul_of_nonneg_left hY hc0
    have hZ0 : 0 ≤ c * max b₁ Y := le_trans (mul_nonneg hc0 hY0) hZ
    refine le_trans (pot_le k F.g1 ha) (max_le ?_ ?_)
    · calc b ≤ c * b := by nlinarith [F.c1]
        _ ≤ c * max b (c * max b₁ Y) := mul_le_mul_of_nonneg_left (le_max_left _ _) hc0
    · calc a ≤ c * Y := haY
        _ ≤ c * (c * Y) := by nlinarith [F.c1]
        _ ≤ c * (c * max b₁ Y) := mul_le_mul_of_nonneg_left hZ hc0
        _ ≤ c * max b (c * max b₁ Y) := mul_le_mul_of_nonneg_left (le_max_right _ _) hc0

theorem phi_upath {c g : ℝ} (F : Facts c g) {M : ℕ → MLine} {n : ℕ} (hp : UPath c M n)
    (h0 : NN (M 0)) : ∀ i, 1 ≤ i → i ≤ n → Φ c g (M 1) ≤ Φ c g (M i) := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  have hnn : ∀ i ≤ n, NN (M i) := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ j ih => intro hj; exact nn_ustep hc0 (hp j (by omega)) (ih (by omega))
  intro i h1 hi
  induction i with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact le_rfl
    · exact le_trans (ih hj (by omega)) (phi_ustep F (hp j (by omega)) (hnn j (by omega)))

theorem first_ustep {c g : ℝ} (F : Facts c g) {a₀ : ℝ} {k : Bool} {L : MLine}
    (h : UStep c ([], k, a₀) L) : c * a₀ ≤ Φ c g L := by
  cases h with
  | base h => exact first_step F h

/-- **Limit theorem with both orientations of the randomized speedup.** Let c > 0 with c² ≥ c + 1
and a₀ ≥ 0. Every quantifier-free line BPTS[n^{a'}] reached from BPTS[n^{a₀}] in n ≥ 1 `UStep`
steps has a' ≥ c·a₀. -/
theorem qf_ge_u {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) {M : ℕ → MLine} {n : ℕ}
    (hp : UPath c M n) (hn : 1 ≤ n) {a₀ a' : ℝ} (ha₀ : 0 ≤ a₀) (h0 : M 0 = ([], true, a₀))
    (hN : M n = ([], true, a')) : c * a₀ ≤ a' := by
  have F := facts_of_phi hc0 hphi
  have hnn0 : NN (M 0) := by rw [h0]; exact ⟨by simp, ha₀⟩
  have h1 : UStep c ([], true, a₀) (M 1) := by rw [← h0]; exact hp 0 (by omega)
  have hf := first_ustep F h1
  have hmono := phi_upath F hp hnn0 n hn le_rfl
  rw [hN] at hmono
  have e : Φ c (1 / (c ^ 2 - 1)) ([], true, a') = a' := rfl
  rw [e] at hmono
  linarith

/-- For c > 0 with c² ≥ c + 1 there is no `URefutes` refutation (from a₀ > 0, non-strict). -/
theorem no_urefutation {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) (n : ℕ) (M : ℕ → MLine) :
    ¬ URefutes c n M := by
  rintro ⟨hn, hp, a₀, a', ha₀, h0, hN, hle⟩
  have := qf_ge_u hc0 hphi hp hn ha₀.le h0 hN
  have hc1 : 1 < c := by nlinarith
  nlinarith


/-! ### Weakening -/

/-- `L'` is a weakening of `L`: the same number of blocks, every output superscript and the kernel
exponent at least those of `L`, and the same kernel type or a BPTS kernel (TS ⊆ BPTS). -/
def Weaker (L L' : MLine) : Prop :=
  List.Forall₂ (· ≤ ·) L.1 L'.1 ∧ (L.2.1 = L'.2.1 ∨ L'.2.1 = true) ∧ L.2.2 ≤ L'.2.2

theorem up_mono_list {c : ℝ} (hc : 0 ≤ c) {l l' : List ℝ} (h : List.Forall₂ (· ≤ ·) l l') :
    ∀ {y y' : ℝ}, y ≤ y' → up c l y ≤ up c l' y' := by
  induction h with
  | nil =>
    intro y y' hy
    simp only [up]
    exact mul_le_mul_of_nonneg_left (max_le_max le_rfl hy) hc
  | cons hb _ ih =>
    intro y y' hy
    simp only [up]
    exact ih (mul_le_mul_of_nonneg_left (max_le_max hb hy) hc)

theorem pot_mono {g b b' a a' : ℝ} (k : Bool) (hg : 0 ≤ g) (hb : b ≤ b') (ha : a ≤ a') :
    pot g b k a ≤ pot g b' k a' := by
  cases k
  · simp only [pot, Bool.false_eq_true, if_false]
    exact max_le_max hb (mul_le_mul_of_nonneg_left ha hg)
  · simp only [pot, if_true]
    exact max_le_max hb ha

/-- **The potential is monotone under weakening.** For `Facts c g` and a line `L` with nonnegative
entries, `Φ c g L ≤ Φ c g L'` for every weakening `L'` of `L`. -/
theorem phi_mono {c g : ℝ} (F : Facts c g) {L L' : MLine} (h : Weaker L L') (hL : NN L) :
    Φ c g L ≤ Φ c g L' := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  obtain ⟨bs, k, a⟩ := L
  obtain ⟨bs', k', a'⟩ := L'
  obtain ⟨hbs, hk, ha⟩ := h
  have ha0 : 0 ≤ a := hL.2
  simp only at hbs hk ha ha0
  cases hbs with
  | nil => exact ha
  | cons hb hrest =>
    simp only [Φ]
    apply up_mono_list hc0 hrest
    rcases hk with rfl | rfl
    · exact pot_mono k F.g0 hb ha
    · refine le_trans (pot_le k F.g1 ha0) ?_
      simp only [pot, if_true]
      exact max_le_max hb ha

theorem nn_weaker {L L' : MLine} (h : Weaker L L') (hL : NN L) : NN L' := by
  obtain ⟨bs, k, a⟩ := L
  obtain ⟨bs', k', a'⟩ := L'
  obtain ⟨hbs, -, ha⟩ := h
  obtain ⟨hb, ha0⟩ := hL
  refine ⟨?_, le_trans ha0 ha⟩
  simp only at hbs hb ⊢
  clear ha ha0
  induction hbs with
  | nil => simp
  | cons hxy _ ih =>
    intro y hy
    simp only [List.mem_cons] at hy hb
    rcases hy with rfl | hy
    · exact le_trans (hb _ (Or.inl rfl)) hxy
    · exact ih (fun z hz => hb z (Or.inr hz)) y hy

/-- `UStep` plus weakening of an existing line. -/
inductive StepW (c : ℝ) : MLine → MLine → Prop
  | rule {L L' : MLine} : UStep c L L' → StepW c L L'
  | weaken {L L' : MLine} : Weaker L L' → StepW c L L'

def PathW (c : ℝ) (M : ℕ → MLine) (n : ℕ) : Prop := ∀ i < n, StepW c (M i) (M (i + 1))

/-- A non-strict refutation with weakening: a `StepW` path BPTS[n^{a₀}] ⊆ … ⊆ BPTS[n^{a'}] with
a₀ > 0 and a' ≤ a₀, in which at least one step is a rule step (MW21's Definition 2.14 asks for a
speedup). -/
def WRefutes (c : ℝ) (n : ℕ) (M : ℕ → MLine) : Prop :=
  PathW c M n ∧ (∃ j < n, UStep c (M j) (M (j + 1))) ∧
    ∃ a₀ a', 0 < a₀ ∧ M 0 = ([], true, a₀) ∧ M n = ([], true, a') ∧ a' ≤ a₀

theorem nn_stepw {c : ℝ} (hc : 0 ≤ c) {L L' : MLine} (h : StepW c L L') (hL : NN L) : NN L' := by
  cases h with
  | rule h => exact nn_ustep hc h hL
  | weaken h => exact nn_weaker h hL

/-- For `Facts c g`, `Φ c g` does not decrease along a `StepW` step from a line with nonnegative
entries. -/
theorem phi_stepw {c g : ℝ} (F : Facts c g) {L L' : MLine} (h : StepW c L L') (hL : NN L) :
    Φ c g L ≤ Φ c g L' := by
  cases h with
  | rule h => exact phi_ustep F h hL
  | weaken h => exact phi_mono F h hL

/-- A `UStep` step from a quantifier-free line reaches a line with at least one block. -/
theorem ustep_nil_ne {c : ℝ} {k : Bool} {a : ℝ} {L : MLine} (h : UStep c ([], k, a) L) :
    L.1 ≠ [] := by
  cases h with
  | base h => cases h with
    | rspeed0 => simp

/-- **Limit theorem with weakening.** Let c > 0 with c² ≥ c + 1 and a₀ ≥ 0. If a `StepW` path
from BPTS[n^{a₀}] to a quantifier-free BPTS[n^{a'}] contains at least one rule step, then
a' ≥ c·a₀. -/
theorem qf_ge_w {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) {M : ℕ → MLine} {n : ℕ}
    (hp : PathW c M n) (hj : ∃ j < n, UStep c (M j) (M (j + 1))) {a₀ a' : ℝ} (ha₀ : 0 ≤ a₀)
    (h0 : M 0 = ([], true, a₀)) (hN : M n = ([], true, a')) : c * a₀ ≤ a' := by
  have F := facts_of_phi hc0 hphi
  have hnn : ∀ i ≤ n, NN (M i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ⟨by simp, ha₀⟩
    | succ j ih => intro hj; exact nn_stepw hc0.le (hp j (by omega)) (ih (by omega))
  have key : ∀ i ≤ n, c * a₀ ≤ Φ c (1 / (c ^ 2 - 1)) (M i) ∨
      ((M i).1 = [] ∧ a₀ ≤ (M i).2.2 ∧ ∀ j < i, ¬ UStep c (M j) (M (j + 1))) := by
    intro i
    induction i with
    | zero =>
      intro _
      right
      rw [h0]
      exact ⟨rfl, le_rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ i ih =>
      intro hi
      have hs := hp i (by omega)
      rcases ih (by omega) with h | ⟨hnil, ha, hno⟩
      · exact Or.inl (le_trans h (phi_stepw F hs (hnn i (by omega))))
      · have hMi : M i = ([], (M i).2.1, (M i).2.2) := Prod.ext hnil rfl
        rw [hMi] at hs
        cases hs with
        | rule u =>
          left
          have h1 := first_ustep F u
          have h2 : c * a₀ ≤ c * (M i).2.2 := mul_le_mul_of_nonneg_left ha hc0.le
          linarith
        | weaken w =>
          right
          obtain ⟨hbs, _, ha'⟩ := w
          have hnil' : (M (i + 1)).1 = [] := List.forall₂_nil_left_iff.mp hbs
          refine ⟨hnil', le_trans ha ha', ?_⟩
          intro j hj hu
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hno j hj hu
          · rw [hMi] at hu
            exact ustep_nil_ne hu hnil'
  rcases key n le_rfl with h | ⟨_, _, hno⟩
  · rw [hN] at h
    exact h
  · obtain ⟨j, hj, hu⟩ := hj
    exact absurd hu (hno j hj)

/-- For c > 0 with c² ≥ c + 1 there is no `WRefutes` refutation (from a₀ > 0, non-strict, with at
least one rule step). -/
theorem no_wrefutation {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) (n : ℕ) (M : ℕ → MLine) :
    ¬ WRefutes c n M := by
  rintro ⟨hp, hj, a₀, a', ha₀, h0, hN, hle⟩
  have := qf_ge_w hc0 hphi hp hj ha₀.le h0 hN
  have hc1 : 1 < c := by nlinarith
  nlinarith


/-! ### Runs of same-type blocks

Read the entries of a line as maximal runs of adjacent same-type blocks, each entry being the output
superscript of the innermost block of its run. Combining or splitting blocks inside a run is then a
weakening (`Weaker`) of the encodings. Two more rules are needed: the same-type unmerged randomized speedup, whose new
n^0 block becomes the innermost block of the run below it (`rspeedS`), and a slowdown that removes
the innermost block of a run of two or more blocks, so that the run stays (`slowIn`). -/

/-- `StepW` plus `rspeedS` and `slowIn`. -/
inductive XStep (c : ℝ) : MLine → MLine → Prop
  | w {L L' : MLine} : StepW c L L' → XStep c L L'
  | rspeedS (b : ℝ) (rest : List ℝ) (k : Bool) (a x b₁ b₂ b₃ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
      (h₁ : 0 ≤ b₁) (h₂ : max b x ≤ b₂) (h₃ : 0 ≤ b₃) (ha : a - x ≤ a₂) :
      XStep c (b :: rest, k, a) (b₃ :: b₂ :: b₁ :: rest, false, a₂)
  | slowIn (b : ℝ) (rest : List ℝ) (k : Bool) (a b' e : ℝ) (h' : 0 ≤ b') (he : c * max b a ≤ e) :
      XStep c (b :: rest, k, a) (b' :: rest, true, e)

def XPath (c : ℝ) (M : ℕ → MLine) (n : ℕ) : Prop := ∀ i < n, XStep c (M i) (M (i + 1))

/-- A non-strict refutation in `XStep`: an `XStep` path BPTS[n^{a₀}] ⊆ … ⊆ BPTS[n^{a'}] with
a₀ > 0 and a' ≤ a₀, in which some line has at least one block (so at least one step is not a
weakening). -/
def XRefutes (c : ℝ) (n : ℕ) (M : ℕ → MLine) : Prop :=
  XPath c M n ∧ (∃ j ≤ n, (M j).1 ≠ []) ∧
    ∃ a₀ a', 0 < a₀ ∧ M 0 = ([], true, a₀) ∧ M n = ([], true, a') ∧ a' ≤ a₀

theorem nn_xstep {c : ℝ} (hc : 0 ≤ c) {L L' : MLine} (h : XStep c L L') (hL : NN L) : NN L' := by
  obtain ⟨hb, ha⟩ := hL
  cases h with
  | w h => exact nn_stepw hc h ⟨hb, ha⟩
  | rspeedS b rest k a x b₁ b₂ b₃ a₂ hx hxa h₁ h₂ h₃ hA =>
    have hb0 : 0 ≤ b := hb b (by simp)
    refine ⟨?_, by simp only at ha ⊢; linarith⟩
    intro y hy; simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | rfl | hy
    · exact h₃
    · exact le_trans (le_trans hb0 (le_max_left _ _)) h₂
    · exact h₁
    · exact hb y (by simp [hy])
  | slowIn b rest k a b' e h' he =>
    have hb0 : 0 ≤ b := hb b (by simp)
    refine ⟨?_, ?_⟩
    · intro y hy; simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h'
      · exact hb y (by simp [hy])
    · simp only at ha ⊢
      have : 0 ≤ c * max b a := mul_nonneg hc (le_trans hb0 (le_max_left _ _))
      linarith

/-- For `Facts c g`, `Φ c g` does not decrease along an `XStep` step from a line with nonnegative
entries. -/
theorem phi_xstep {c g : ℝ} (F : Facts c g) {L L' : MLine} (h : XStep c L L') (hL : NN L) :
    Φ c g L ≤ Φ c g L' := by
  have hc0 : 0 ≤ c := by linarith [F.c1]
  cases h with
  | w h => exact phi_stepw F h hL
  | rspeedS b rest k a x b₁ b₂ b₃ a₂ hx hxa h₁ h₂ h₃ hA =>
    obtain ⟨hb, ha⟩ := hL
    simp only at ha
    simp only [Φ, up]
    apply up_mono hc0
    have hb0 : 0 ≤ b := hb b (by simp)
    have hp : g * (a - x) ≤ pot g b₃ false a₂ :=
      le_trans (mul_le_mul_of_nonneg_left hA F.g0) pot_d_ge
    have hY : c * max x (g * (a - x)) ≤ c * max b₂ (pot g b₃ false a₂) :=
      mul_le_mul_of_nonneg_left (max_le_max (le_trans (le_max_right _ _) h₂) hp) hc0
    have hk := key_r F hx hxa
    set Y := c * max b₂ (pot g b₃ false a₂) with hYdef
    have hbY : b ≤ Y := by
      have hb2 : b ≤ b₂ := le_trans (le_max_left _ _) h₂
      have : b₂ ≤ max b₂ (pot g b₃ false a₂) := le_max_left _ _
      nlinarith [F.c1]
    have hY0 : 0 ≤ Y := le_trans hb0 hbY
    have hZ : c * Y ≤ c * max b₁ Y := mul_le_mul_of_nonneg_left (le_max_right _ _) hc0
    have hcY : Y ≤ c * Y := by nlinarith [F.c1]
    refine le_trans (pot_le k F.g1 ha) (max_le ?_ ?_)
    · linarith
    · calc a ≤ c ^ 2 * max x (g * (a - x)) := hk
        _ = c * (c * max x (g * (a - x))) := by ring
        _ ≤ c * Y := mul_le_mul_of_nonneg_left hY hc0
        _ ≤ c * max b₁ Y := hZ
  | slowIn b rest k a b' e h' he =>
    obtain ⟨hb, ha⟩ := hL
    simp only at ha
    simp only [Φ]
    apply up_mono hc0
    have hb0 : 0 ≤ b := hb b (by simp)
    have hm0 : 0 ≤ max b a := le_trans hb0 (le_max_left _ _)
    have hcm : max b a ≤ c * max b a := by nlinarith [F.c1]
    simp only [pot, if_true]
    exact le_trans (pot_le k F.g1 ha) (le_trans hcm (le_trans he (le_max_right _ _)))

theorem xstep_nil {c : ℝ} {k : Bool} {a : ℝ} {L : MLine} (h : XStep c ([], k, a) L) :
    StepW c ([], k, a) L := by
  cases h with
  | w h => exact h

/-- **Limit theorem for `XStep`.** Let c > 0 with c² ≥ c + 1 and a₀ ≥ 0. If an `XStep` path from
BPTS[n^{a₀}] to a quantifier-free BPTS[n^{a'}] passes through a line with at least one block, then
a' ≥ c·a₀. -/
theorem qf_ge_x {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) {M : ℕ → MLine} {n : ℕ}
    (hp : XPath c M n) (hj : ∃ j ≤ n, (M j).1 ≠ []) {a₀ a' : ℝ} (ha₀ : 0 ≤ a₀)
    (h0 : M 0 = ([], true, a₀)) (hN : M n = ([], true, a')) : c * a₀ ≤ a' := by
  have F := facts_of_phi hc0 hphi
  have hnn : ∀ i ≤ n, NN (M i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact ⟨by simp, ha₀⟩
    | succ j ih => intro hj; exact nn_xstep hc0.le (hp j (by omega)) (ih (by omega))
  have key : ∀ i ≤ n, c * a₀ ≤ Φ c (1 / (c ^ 2 - 1)) (M i) ∨
      (a₀ ≤ (M i).2.2 ∧ ∀ j ≤ i, (M j).1 = []) := by
    intro i
    induction i with
    | zero =>
      intro _
      right
      rw [h0]
      refine ⟨le_rfl, fun j hj => ?_⟩
      rw [Nat.le_zero.mp hj, h0]
    | succ i ih =>
      intro hi
      have hs := hp i (by omega)
      rcases ih (by omega) with h | ⟨ha, hno⟩
      · exact Or.inl (le_trans h (phi_xstep F hs (hnn i (by omega))))
      · have hMi : M i = ([], (M i).2.1, (M i).2.2) := Prod.ext (hno i le_rfl) rfl
        rw [hMi] at hs
        cases xstep_nil hs with
        | rule u =>
          left
          have h1 := first_ustep F u
          have h2 : c * a₀ ≤ c * (M i).2.2 := mul_le_mul_of_nonneg_left ha hc0.le
          linarith
        | weaken w =>
          right
          obtain ⟨hbs, _, ha'⟩ := w
          have hnil' : (M (i + 1)).1 = [] := List.forall₂_nil_left_iff.mp hbs
          refine ⟨le_trans ha ha', fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hj | rfl
          · exact hno j (by omega)
          · exact hnil'
  rcases key n le_rfl with h | ⟨_, hno⟩
  · rw [hN] at h
    exact h
  · obtain ⟨j, hj, hne⟩ := hj
    exact absurd (hno j hj) hne

/-- For c > 0 with c² ≥ c + 1 there is no `XRefutes` refutation (from a₀ > 0, non-strict, through
a line with a block). -/
theorem no_xrefutation {c : ℝ} (hc0 : 0 < c) (hphi : c + 1 ≤ c ^ 2) (n : ℕ) (M : ℕ → MLine) :
    ¬ XRefutes c n M := by
  rintro ⟨hp, hj, a₀, a', ha₀, h0, hN, hle⟩
  have := qf_ge_x hc0 hphi hp hj ha₀.le h0 hN
  have hc1 : 1 < c := by nlinarith
  nlinarith

end MW
end PastaMath.MWThreshold
