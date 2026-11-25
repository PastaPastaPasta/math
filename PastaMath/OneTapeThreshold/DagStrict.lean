-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The DAG checker for the strict reading of Lemma 3.3

The checker of `Dag.lean` for a stricter reading of the calculus: every line of the derivation
has kernel time ≥ its input superscript (`pin ≤ time`) and, on DTISP kernels, space ≤ time (`SpOK`).
The second condition is what the CMU full version of Williams's paper requires of a DTISP kernel in
its slowdown lemma; the TOCT Lemma 7.2 states "all e ≥ 0".

The claims, moves and checker are those of `Dag.lean` with these changes: `Der` requires
`pin ≤ time` and `SpOK` on every line after the first; claims assume u.o ≤ a and (for DTISP
kernels) e ≤ a on their first line and guarantee pin rest ≤ a'; a speedup is clipped at
x ≤ a − max(e, u.o, 1); chain positions must stay ≥ M (κ' ≥ 1); Lemma 7.1 picks s ≤ a/d.
`dagCheck_sound`: acceptance gives `∃ Mp n, HY.NF c d Mp n ∧ ∀ i ≤ n, pin ≤ time ∧ SpOK` on
`Mp i`. As in `Dag.lean`, everything is proved for `HY.StepO ℓ` with `HY.LogOK ℓ` (here the output ℓ of
the new log n block is also at most the new kernel time, since it is at most max(u.o, e)):
`dagCheck_soundO` gives `HY.NFO ℓ`, `dagCheck_sound` is ℓ = max and `dagCheck_sound1` is ℓ = 1.
-/

namespace PastaMath.OneTapeThreshold
namespace HDS

open HY

/-- Space ≤ time on a DTISP kernel (no condition on a DTIME_d kernel). -/
def SpOK : Ker → Prop
  | .T _ => True
  | .S a e => e ≤ a

/-- The block list alternates and every block has 1 ≤ o and 0 ≤ g ≤ o. -/
def Good (bl : List Blk) : Prop := Alt bl ∧ ∀ u ∈ bl, 1 ≤ u.o ∧ 0 ≤ u.g ∧ u.g ≤ u.o

/-- A `HY.StepO ℓ c d` derivation whose lines after the first have nonempty, alternating block lists,
kernel time ≥ input superscript, and `SpOK`. -/
inductive Der (ℓ : ℝ → ℝ → ℝ) (c d : ℝ) : Line → Line → Prop
  | refl (L : Line) : Der ℓ c d L L
  | cons {L L' L'' : Line} : StepO ℓ c d L L' → L'.1 ≠ [] → Alt L'.1 → pin L'.1 ≤ L'.2.time →
      SpOK L'.2 → Der ℓ c d L' L'' → Der ℓ c d L L''

/-- Strict S-claim: for every scale B ≥ B0 and every line `(u :: rest, S a e)` with `Good (u :: rest)`,
u.o ≤ B, 1 ≤ a ≤ κ·B, 0 ≤ e ≤ ε·B, u.o ≤ a and e ≤ a, there are a' with 1 ≤ a', pin rest ≤ a' and
a' ≤ c·max (pin rest) (V·B), a `Der` derivation from that line to some `Lp`, and a `HY.StepO ℓ c d` step from `Lp` to
`(rest, T a')`. -/
def SC (ℓ : ℝ → ℝ → ℝ) (c d B0 κ ε V : ℝ) : Prop :=
  ∀ B, B0 ≤ B → ∀ (u : Blk) (rest : List Blk) (a e : ℝ), Good (u :: rest) → u.o ≤ B → 1 ≤ a →
    a ≤ κ * B → 0 ≤ e → e ≤ ε * B → u.o ≤ a → e ≤ a →
    ∃ a', 1 ≤ a' ∧ pin rest ≤ a' ∧ a' ≤ c * max (pin rest) (V * B) ∧
      ∃ Lp, Der ℓ c d (u :: rest, .S a e) Lp ∧ StepO ℓ c d Lp (rest, .T a')

/-- Strict T-claim: as `SC`, for lines `(u :: rest, T a)` with `Good (u :: rest)`, u.o ≤ B,
1 ≤ a ≤ α·B and u.o ≤ a. -/
def TC (ℓ : ℝ → ℝ → ℝ) (c d B0 α V : ℝ) : Prop :=
  ∀ B, B0 ≤ B → ∀ (u : Blk) (rest : List Blk) (a : ℝ), Good (u :: rest) → u.o ≤ B → 1 ≤ a →
    a ≤ α * B → u.o ≤ a →
    ∃ a', 1 ≤ a' ∧ pin rest ≤ a' ∧ a' ≤ c * max (pin rest) (V * B) ∧
      ∃ Lp, Der ℓ c d (u :: rest, .T a) Lp ∧ StepO ℓ c d Lp (rest, .T a')

section sem

variable {ℓ : ℝ → ℝ → ℝ} {c d : ℝ}

/-- Derivations compose. -/
theorem Der.trans {L L' L'' : Line} (h₁ : Der ℓ c d L L') (h₂ : Der ℓ c d L' L'') : Der ℓ c d L L'' := by
  induction h₁ with
  | refl _ => exact h₂
  | cons hs hne halt hpt hsp _ ih => exact Der.cons hs hne halt hpt hsp (ih h₂)

theorem Der.snoc {L L' L'' L''' : Line} (h₁ : Der ℓ c d L L') (hs : StepO ℓ c d L' L'') (hne : L''.1 ≠ [])
    (halt : Alt L''.1) (hpt : pin L''.1 ≤ L''.2.time) (hsp : SpOK L''.2) (h₂ : Der ℓ c d L'' L''') :
    Der ℓ c d L L''' :=
  h₁.trans (Der.cons hs hne halt hpt hsp h₂)

theorem Good.tail {u : Blk} {rest : List Blk} (h : Good (u :: rest)) : Good rest := by
  refine ⟨?_, fun v hv => h.2 v (by simp [hv])⟩
  have := h.1
  cases rest with
  | nil => trivial
  | cons v vs => exact this.2

theorem Good.head {u : Blk} {rest : List Blk} (h : Good (u :: rest)) : 1 ≤ u.o ∧ 0 ≤ u.g ∧ u.g ≤ u.o :=
  h.2 u (by simp)

theorem pin_ge {bl : List Blk} (h : Good bl) : 1 ≤ pin bl := by
  cases bl with
  | nil => simp [pin]
  | cons u _ => exact (h.head).1

/-- Alternation only depends on the quantifier types. -/
theorem alt_cons_q {u v : Blk} {rest : List Blk} (hq : u.q = v.q) (h : Alt (u :: rest)) :
    Alt (v :: rest) := by
  cases rest with
  | nil => trivial
  | cons w ws => exact ⟨by rw [← hq]; exact h.1, h.2⟩

/-- The final Lemma 7.2 step of a level, with its cost bound. -/
theorem pop_step (_hc : 0 ≤ c) {u : Blk} {rest : List Blk} {k : Ker} (hg : Good (u :: rest))
    (hk : 1 ≤ k.time) :
    StepO ℓ c d (u :: rest, k) (rest, .T (c * max (max (pin rest) u.o) (max u.g k.time))) :=
  StepO.slow u rest k (pin_ge hg.tail) hg.head.1 hk hg.head.2.1

theorem pop_bound (hc : 0 ≤ c) {u : Blk} {rest : List Blk} {t W : ℝ} (hg : Good (u :: rest))
    (ho : u.o ≤ W) (ht : t ≤ W) :
    c * max (max (pin rest) u.o) (max u.g t) ≤ c * max (pin rest) W := by
  apply mul_le_mul_of_nonneg_left _ hc
  have := hg.head
  refine max_le (max_le (le_max_left _ _) (le_trans ho (le_max_right _ _)))
    (max_le (le_trans (le_trans this.2.2 ho) (le_max_right _ _)) (le_trans ht (le_max_right _ _)))

theorem pop_pin (hc : 1 ≤ c) {u : Blk} {rest : List Blk} {t : ℝ} (hg : Good (u :: rest)) :
    pin rest ≤ c * max (max (pin rest) u.o) (max u.g t) := by
  have h1 := pin_ge hg.tail
  have : pin rest ≤ max (max (pin rest) u.o) (max u.g t) := le_trans (le_max_left _ _) (le_max_left _ _)
  nlinarith

theorem pop_ge (hc : 1 ≤ c) {u : Blk} {rest : List Blk} {t : ℝ} (hg : Good (u :: rest)) :
    1 ≤ c * max (max (pin rest) u.o) (max u.g t) := by
  have h1 := pin_ge hg.tail
  have : 1 ≤ max (max (pin rest) u.o) (max u.g t) := le_trans h1 (le_trans (le_max_left _ _) (le_max_left _ _))
  nlinarith

/-- For c ≥ 1 and B0 ≥ 0, closing the level at once (one Lemma 7.2 step) proves
`SC ℓ c d B0 κ ε (max 1 κ)`. -/
theorem SC_pop (hc : 1 ≤ c) {B0 κ ε : ℝ} (hB0 : 0 ≤ B0) : SC ℓ c d B0 κ ε (max 1 κ) := by
  intro B hB u rest a e hg ho ha haκ _ _ _ _
  have hB' : 0 ≤ B := le_trans hB0 hB
  refine ⟨_, pop_ge hc hg, pop_pin hc hg, pop_bound (by linarith) hg ?_ ?_, _, Der.refl _, pop_step (by linarith) hg ha⟩
  · exact le_trans ho (by nlinarith [le_max_left 1 κ])
  · show a ≤ max 1 κ * B
    exact le_trans haκ (mul_le_mul_of_nonneg_right (le_max_right _ _) hB')

/-- For c ≥ 1 and B0 ≥ 0, closing the level at once proves `TC ℓ c d B0 α (max 1 α)`. -/
theorem TC_pop (hc : 1 ≤ c) {B0 α : ℝ} (hB0 : 0 ≤ B0) : TC ℓ c d B0 α (max 1 α) := by
  intro B hB u rest a hg ho ha haα _
  have hB' : 0 ≤ B := le_trans hB0 hB
  refine ⟨_, pop_ge hc hg, pop_pin hc hg, pop_bound (by linarith) hg ?_ ?_, _, Der.refl _, pop_step (by linarith) hg ha⟩
  · exact le_trans ho (by nlinarith [le_max_left 1 α])
  · show a ≤ max 1 α * B
    exact le_trans haα (mul_le_mul_of_nonneg_right (le_max_right _ _) hB')

/-- For B0 ≥ 0 and c ≥ 0, an S-claim with value V is an S-claim with every value V' ≥ V. -/
theorem SC_mono {B0 κ ε V V' : ℝ} (hB0 : 0 ≤ B0) (hc : 0 ≤ c) (hV : V ≤ V') (h : SC ℓ c d B0 κ ε V) :
    SC ℓ c d B0 κ ε V' := by
  intro B hB u rest a e hg ho ha haκ he heε hst hea
  obtain ⟨a', h1, hp, h2, rest'⟩ := h B hB u rest a e hg ho ha haκ he heε hst hea
  refine ⟨a', h1, hp, le_trans h2 (mul_le_mul_of_nonneg_left (max_le_max le_rfl ?_) hc), rest'⟩
  exact mul_le_mul_of_nonneg_right hV (le_trans hB0 hB)

/-- For B0 ≥ 0 and c ≥ 0, a T-claim with value V is a T-claim with every value V' ≥ V. -/
theorem TC_mono {B0 α V V' : ℝ} (hB0 : 0 ≤ B0) (hc : 0 ≤ c) (hV : V ≤ V') (h : TC ℓ c d B0 α V) :
    TC ℓ c d B0 α V' := by
  intro B hB u rest a hg ho ha haα hst
  obtain ⟨a', h1, hp, h2, rest'⟩ := h B hB u rest a hg ho ha haα hst
  refine ⟨a', h1, hp, le_trans h2 (mul_le_mul_of_nonneg_left (max_le_max le_rfl ?_) hc), rest'⟩
  exact mul_le_mul_of_nonneg_right hV (le_trans hB0 hB)

/-- Lemma 7.1, merged: for B0 ≥ 0, d ≥ 1, κ ≥ 1, 0 < ε ≤ 1 and d·(κ − 1) ≤ ε, an S-claim
`SC ℓ c d B0 κ ε Ω` gives `TC ℓ c d B0 α (Ω/κ·α)` for every α ≥ κ. -/
theorem TC_of_SC {B0 κ ε Ω : ℝ} (hB0 : 0 ≤ B0) (hd1 : 1 ≤ d) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hdε : d * (κ - 1) ≤ ε) (h : SC ℓ c d B0 κ ε Ω) {α : ℝ} (hα : κ ≤ α) :
    TC ℓ c d B0 α (Ω / κ * α) := by
  intro B hB u rest a hg ho ha haα hst
  have hB' : 0 ≤ B := le_trans hB0 hB
  have hκ0 : 0 < κ := by linarith
  set β := α * B / κ with hβ
  have hβB : B ≤ β := by
    rw [hβ, le_div_iff₀ hκ0]; nlinarith
  have hβ0 : 0 ≤ β := le_trans hB' hβB
  have hκβ : κ * β = α * B := by rw [hβ]; field_simp
  have hd : 0 < d := by linarith
  obtain ⟨s, hs0, hsa, htop, hspace, hsp⟩ :
      ∃ s : ℝ, 0 < s ∧ s ≤ a ∧ a - s ≤ β ∧ d * s ≤ ε * β ∧ d * s ≤ a := by
    rcases le_or_gt a β with hab | hab
    · have hβpos : 0 < β := by linarith
      refine ⟨min (a / d) (ε * β / d), lt_min (div_pos (by linarith) hd) (div_pos (mul_pos hε hβpos) hd),
        le_trans (min_le_left _ _) (div_le_self (by linarith) hd1), ?_, ?_, ?_⟩
      · have : 0 ≤ min (a / d) (ε * β / d) := le_min (div_nonneg (by linarith) hd.le)
          (div_nonneg (mul_nonneg hε.le hβ0) hd.le)
        linarith
      · calc d * min (a / d) (ε * β / d) ≤ d * (ε * β / d) := mul_le_mul_of_nonneg_left (min_le_right _ _) hd.le
          _ = ε * β := by field_simp
      · calc d * min (a / d) (ε * β / d) ≤ d * (a / d) := mul_le_mul_of_nonneg_left (min_le_left _ _) hd.le
          _ = a := by field_simp
    · have hsp0 : d * (a - β) ≤ ε * β := by
        have : a - β ≤ (κ - 1) * β := by nlinarith
        calc d * (a - β) ≤ d * ((κ - 1) * β) := mul_le_mul_of_nonneg_left this hd.le
          _ = d * (κ - 1) * β := by ring
          _ ≤ ε * β := mul_le_mul_of_nonneg_right hdε hβ0
      refine ⟨a - β, by linarith, by linarith, by linarith, hsp0, ?_⟩
      have : ε * β ≤ β := by nlinarith
      linarith
  have hstep := StepO.convMerge (ℓ := ℓ) (c := c) (d := d) u rest a s hs0 hsa hg.head.1
  set u' : Blk := ⟨u.q, max u.g (a - s), max (a - s) u.o⟩ with hu'
  have hg' : Good (u' :: rest) := by
    refine ⟨alt_cons_q (u := u) (v := u') rfl hg.1, ?_⟩
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · have := hg.head
      refine ⟨le_trans this.1 (le_max_right _ _), le_trans this.2.1 (le_max_left _ _), ?_⟩
      exact max_le (le_trans this.2.2 (le_max_right _ _)) (le_max_left _ _)
    · exact hg.2 v (by simp [hv])
  have ho' : u'.o ≤ β := max_le htop (le_trans ho hβB)
  have hst' : u'.o ≤ a := max_le (by linarith) hst
  obtain ⟨a', h1, hp, h2, Lp, hder, hfin⟩ :=
    h β (le_trans hB hβB) u' rest a (d * s) hg' ho' ha (by rw [hκβ]; exact haα)
      (mul_nonneg hd.le hs0.le) hspace hst' hsp
  refine ⟨a', h1, hp, ?_, Lp, Der.cons hstep (by simp) hg'.1 hst' hsp hder, hfin⟩
  have : Ω * β = Ω / κ * α * B := by rw [hβ]; field_simp
  rw [this] at h2; exact h2

/-- Lemma 3.3, merged: for c ≥ 1 and B0 ≥ 0, from an inner S-claim `SC ℓ c d B0 κ' ε W` and an
outer T-claim `TC ℓ c d B0 α VT`, with 1 ≤ u, ε ≤ u, κ' = κ + ε − u, ε ≤ κ', 1 ≤ κ', ε ≤ 1, 0 ≤ ε,
1 ≤ κ'·B0, c·max(u, W) ≤ α·u and 1 ≤ u·VT, follows `SC ℓ c d B0 κ ε (u·VT)`. -/
theorem SC_speed (hℓ : LogOK ℓ) (hc : 1 ≤ c) {B0 κ κ' ε u W α VT : ℝ} (hB0 : 0 ≤ B0)
    (hinner : SC ℓ c d B0 κ' ε W) (houter : TC ℓ c d B0 α VT)
    (hu : 1 ≤ u) (hεu : ε ≤ u) (hκ' : κ' = κ + ε - u) (hεκ' : ε ≤ κ') (hκ1 : 1 ≤ κ') (hε1 : ε ≤ 1)
    (hε0 : 0 ≤ ε) (hfl : 1 ≤ κ' * B0) (hα : c * max u W ≤ α * u) (_hV1 : 1 ≤ u * VT) :
    SC ℓ c d B0 κ ε (u * VT) := by
  intro B hB u0 rest a e hg ho ha haκ he heε hst hae
  have hB' : 0 ≤ B := le_trans hB0 hB
  have hc0 : 0 ≤ c := by linarith
  set m1 := max (max e u0.o) 1 with hm1def
  set x := min ((u - ε) * B) (a - m1) with hx
  have hm1 : m1 ≤ a := max_le (max_le hae hst) ha
  have hx0 : 0 ≤ x := le_min (mul_nonneg (by linarith) hB') (by linarith)
  have hxa : x ≤ a - m1 := min_le_right _ _
  have hxp : x ≤ (u - ε) * B := min_le_left _ _
  have hme : e ≤ m1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hmo1 : u0.o ≤ m1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hm11 : 1 ≤ m1 := le_max_right _ _
  have hex : e ≤ a - x := by linarith
  have hx1 : x ≤ a - 1 := by linarith
  have hstep := StepO.speedMerge (ℓ := ℓ) (c := c) (d := d) u0 rest a e x ha he hex hx0 hx1 hg.head.1
  set lo : Blk := ⟨!u0.q, 0, ℓ u0.o e⟩
  have hℓe := hℓ u0.o e hg.head.1 he
  set mo : Blk := ⟨u0.q, max u0.g (x + e), max u0.o (x + e)⟩
  have hgm : Good (mo :: rest) := by
    refine ⟨alt_cons_q (u := u0) (v := mo) rfl hg.1, ?_⟩
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · have := hg.head
      refine ⟨le_trans this.1 (le_max_left _ _), le_trans this.2.1 (le_max_left _ _), ?_⟩
      exact max_le (le_trans this.2.2 (le_max_left _ _)) (le_max_right _ _)
    · exact hg.2 v (by simp [hv])
  have hgl : Good (lo :: mo :: rest) := by
    refine ⟨⟨by simp [lo, mo], hgm.1⟩, ?_⟩
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨hℓe.1, le_rfl, by linarith [hℓe.1]⟩
    · exact hgm.2 v (by simpa using hv)
  have hlo : lo.o ≤ B := le_trans hℓe.2 (max_le ho (le_trans heε (by nlinarith)))
  have hlost : lo.o ≤ a - x := by
    show ℓ u0.o e ≤ a - x
    exact le_trans hℓe.2 (max_le (by linarith) (by linarith))
  have hin1 : 1 ≤ a - x := by linarith
  have hinκ : a - x ≤ κ' * B := by
    rcases le_total ((u - ε) * B) (a - m1) with h | h
    · have : x = (u - ε) * B := min_eq_left h
      rw [this, hκ']; nlinarith
    · have : x = a - m1 := min_eq_right h
      rw [this]
      have h1 : e ≤ κ' * B := le_trans heε (mul_le_mul_of_nonneg_right hεκ' hB')
      have h2 : 1 ≤ κ' * B := le_trans hfl (mul_le_mul_of_nonneg_left hB (le_trans hε0 hεκ'))
      have h3 : u0.o ≤ κ' * B := le_trans ho (by nlinarith)
      have : a - (a - m1) = m1 := by ring
      rw [this]; exact max_le (max_le h1 h3) h2
  obtain ⟨a₁, h1₁, hp₁, h2₁, Lp₁, hder₁, hfin₁⟩ :=
    hinner B hB lo (mo :: rest) (a - x) e hgl hlo hin1 hinκ he heε hlost hex
  have huB : B ≤ u * B := by nlinarith
  have hmo : mo.o ≤ u * B := max_le (le_trans ho huB) (by nlinarith)
  have ha₁ : a₁ ≤ α * (u * B) := by
    have : c * max (pin (mo :: rest)) (W * B) ≤ c * (max u W * B) := by
      apply mul_le_mul_of_nonneg_left _ hc0
      show max mo.o (W * B) ≤ max u W * B
      rw [max_mul_of_nonneg _ _ hB']
      exact max_le_max hmo le_rfl
    have h3 : c * (max u W * B) = (c * max u W) * B := by ring
    have h4 : (c * max u W) * B ≤ (α * u) * B := mul_le_mul_of_nonneg_right hα hB'
    linarith [show α * (u * B) = (α * u) * B by ring]
  have hmost : mo.o ≤ a₁ := hp₁
  obtain ⟨a₂, h1₂, hp₂, h2₂, Lp₂, hder₂, hfin₂⟩ :=
    houter (u * B) (le_trans hB huB) mo rest a₁ hgm hmo h1₁ ha₁ hmost
  refine ⟨a₂, h1₂, hp₂, by rw [show u * VT * B = VT * (u * B) by ring]; exact h2₂, Lp₂, ?_, hfin₂⟩
  exact Der.cons hstep (by simp) hgl.1 hlost hex (Der.snoc hder₁ hfin₁ (by simp) hgm.1 hmost trivial hder₂)

/-- A `Der` derivation gives an indexed `HY.StepO ℓ c d` path whose lines after the first have nonempty,
alternating block lists, kernel time ≥ input superscript, and `SpOK`. -/
theorem der_path {L L' : Line} (h : Der ℓ c d L L') :
    ∃ n, ∃ M : ℕ → Line, M 0 = L ∧ M n = L' ∧ Path (StepO ℓ c d) M n ∧
      ∀ i, 0 < i → i ≤ n → (M i).1 ≠ [] ∧ Alt (M i).1 ∧ pin (M i).1 ≤ (M i).2.time ∧ SpOK (M i).2 := by
  induction h with
  | refl L => exact ⟨0, fun _ => L, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun i h1 h2 => by omega⟩
  | @cons L L' L'' hs hne halt hpt hsp _ ih =>
    obtain ⟨n, M, h0, hn, hp, hP⟩ := ih
    refine ⟨n + 1, fun i => if i = 0 then L else M (i - 1), by simp, by simp [hn], ?_, ?_⟩
    · intro i hi
      rcases i with _ | i
      · simp [h0, hs]
      · simpa using hp i (by omega)
    · intro i h1 h2
      rcases i with _ | i
      · omega
      · rcases i with _ | i
        · simp [h0, hne, halt, hpt, hsp]
        · simpa using hP (i + 1) (by omega) (by omega)

/-- For c ≥ 1, B0 ≥ 0, d ≥ 0, κ > 1, d·(κ − 1) ≤ ε ≤ 1, V ≥ 1 and c·V < κ, an S-claim
`SC ℓ c d B0 κ ε V` gives a strict normal-form proof `HY.NFO ℓ c d M n` with `pin ≤ time` and `SpOK` on every
line `M i`, i ≤ n. -/
theorem nf_of_SC (_hc : 1 ≤ c) {B0 κ ε V : ℝ} (_hB0 : 0 ≤ B0) (hd : 0 ≤ d) (hκ : 1 < κ)
    (hdε : d * (κ - 1) ≤ ε) (hε1 : ε ≤ 1) (hV : 1 ≤ V) (hcV : c * V < κ) (h : SC ℓ c d B0 κ ε V) :
    ∃ M n, HY.NFO ℓ c d M n ∧ ∀ i ≤ n, pin (M i).1 ≤ (M i).2.time ∧ SpOK (M i).2 := by
  set β := max B0 1 with hβ
  have hβ1 : 1 ≤ β := le_max_right _ _
  set a0 := κ * β
  have hs0 : 0 < a0 - β := by nlinarith
  have hstep := StepO.convNew (ℓ := ℓ) (c := c) (d := d) [] true a0 (a0 - β)
    (fun u rest h => by simp at h) hs0 (by nlinarith) (by simp [pin])
  set u : Blk := ⟨true, a0 - (a0 - β), max (a0 - (a0 - β)) (pin [])⟩
  have huo : u.o = β := by simp [u, pin, max_eq_left hβ1]
  have hg : Good [u] := by
    refine ⟨trivial, ?_⟩
    intro v hv; simp only [List.mem_singleton] at hv; subst hv
    refine ⟨by rw [huo]; exact hβ1, by simp [u]; linarith, ?_⟩
    simp [u]
  have huo' : u.o ≤ a0 := by rw [huo]; simp only [a0]; nlinarith
  have hsp0 : d * (a0 - β) ≤ a0 := by
    have : d * (a0 - β) = d * (κ - 1) * β := by simp only [a0]; ring
    rw [this]
    have h1 : d * (κ - 1) * β ≤ ε * β := mul_le_mul_of_nonneg_right hdε (by linarith)
    have h2 : ε * β ≤ β := by nlinarith
    simp only [a0]; nlinarith
  obtain ⟨a', h1, _, h2, Lp, hder, hfin⟩ :=
    h β (le_max_left _ _) u [] a0 (d * (a0 - β)) hg (le_of_eq huo) (by nlinarith) le_rfl
      (mul_nonneg hd hs0.le) (by
        have : d * (a0 - β) = d * (κ - 1) * β := by simp only [a0]; ring
        rw [this]; exact mul_le_mul_of_nonneg_right hdε (by linarith)) huo' hsp0
  have hlt : a' < a0 := by
    have hVβ : 1 ≤ V * β := by nlinarith
    simp only [pin] at h2
    rw [max_eq_right hVβ] at h2
    have : c * (V * β) < κ * β := by nlinarith
    linarith
  have hder' : Der ℓ c d ([], .T a0) Lp := Der.cons hstep (by simp) trivial (by simpa [pin, Ker.time] using huo') hsp0 hder
  obtain ⟨n, M, h0, hn, hp, hP⟩ := der_path hder'
  refine ⟨fun i => if i ≤ n then M i else ([], .T a'), n + 1, ?_, ?_⟩
  swap
  · intro i hi
    by_cases hin : i ≤ n
    · rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp only [Nat.zero_le, ↓reduceIte, h0, pin, Ker.time, SpOK]
        exact ⟨by nlinarith, trivial⟩
      · simpa [hin] using (hP i h hin).2.2
    · simpa [hin, pin, Ker.time, SpOK] using h1
  refine ⟨by omega, ?_, ⟨a0, by simp [h0]⟩, ⟨a', by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hin : i < n
    · simpa [show i ≤ n by omega, show i + 1 ≤ n by omega] using hp i hin
    · have : i = n := by omega
      subst this
      simpa [hn] using hfin
  · intro i h1 h2
    simpa [show i ≤ n by omega] using (hP i h1 (by omega)).1
  · simpa [Ker.time] using h1
  · simpa [Ker.time, h0] using hlt
  · intro i hi
    by_cases hin : i ≤ n
    · rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp [h0, Alt]
      · simpa [hin] using (hP i h hin).2.1
    · simp [hin, Alt]

end sem

/-- A node: grid index `t` (κ = t/M, ε = d·(t − M)/M), claimed ratio φ = `phi`/2^SH, the
expected final kernel position `p`, and the chain of Lemma 3.3 steps: per step the top index `ku`
(u = ku/M), the closing of the outer T-level (`r = 0`: Lemma 7.2 at once; otherwise the (r − 1)-th
node of the table) and the claimed value `w`/2^SH at that step. -/
structure Node where
  t : ℕ
  p : ℕ
  phi : ℕ
  steps : List (ℕ × ℕ × ℕ)

/-- The value of closing a T-level with kernel ratio α: max(1, α) for `r = 0`; φ_r·α for node r − 1 if its
κ ≤ α; `none` otherwise. -/
def tval (M : ℕ) (tab : List (ℕ × ℚ)) (r : ℕ) (α : ℚ) : Option ℚ :=
  if r = 0 then some (max 1 α) else
    match tab[r - 1]? with
    | none => none
    | some (tr, φ) => if (tr : ℚ) / M ≤ α then some (φ * α) else none

/-- Evaluates a chain from kernel position j (steps move the position from j to j + i − ku) and checks
every claimed value; `none` if a check fails. -/
def chain (c : ℚ) (M i p SH : ℕ) (tab : List (ℕ × ℚ)) : ℕ → List (ℕ × ℕ × ℕ) → Option ℚ
  | j, [] => if j = p then some (max 1 ((j : ℚ) / M)) else none
  | j, (ku, r, w) :: rest =>
      if M ≤ ku ∧ i ≤ ku ∧ ku ≤ j ∧ M ≤ j + i - ku then
        match chain c M i p SH tab (j + i - ku) rest with
        | none => none
        | some W =>
          match tval M tab r (c * max 1 (W / ((ku : ℚ) / M))) with
          | none => none
          | some v =>
            if 1 ≤ (ku : ℚ) / M * v ∧ (ku : ℚ) / M * v ≤ (w : ℚ) / 2 ^ SH then some ((w : ℚ) / 2 ^ SH)
            else none
      else none

/-- Checks the nodes in order and appends each accepted (t, φ) to the table. -/
def procNodes (c : ℚ) (d M SH : ℕ) : List (ℕ × ℚ) → List Node → Option (List (ℕ × ℚ))
  | tab, [] => some tab
  | tab, nd :: rest =>
      if M < nd.t ∧ d * (nd.t - M) ≤ M then
        match chain c M (d * (nd.t - M)) nd.p SH tab nd.t nd.steps with
        | none => none
        | some W =>
          if W / ((nd.t : ℚ) / M) ≤ (nd.phi : ℚ) / 2 ^ SH ∧ 1 ≤ (nd.phi : ℚ) / 2 ^ SH * ((nd.t : ℚ) / M)
          then procNodes c d M SH (tab ++ [(nd.t, (nd.phi : ℚ) / 2 ^ SH)]) rest
          else none
      else none

/-- Accepts when 1 ≤ c, 1 ≤ d, 1 ≤ M, every node passes `procNodes` and the root node has c·φ < 1. -/
def dagCheck (c : ℚ) (d M SH : ℕ) (nodes : List Node) (root : ℕ) : Bool :=
  decide (1 ≤ c) && decide (1 ≤ d) && decide (1 ≤ M) &&
  match procNodes c d M SH [] nodes with
  | none => false
  | some tab =>
    match tab[root]? with
    | none => false
    | some (_, φ) => decide (c * φ < 1)

section sound

variable {ℓ : ℝ → ℝ → ℝ} {cq : ℚ} {d M SH : ℕ}

/-- Every table entry (t, φ) has M < t, d·(t − M) ≤ M, φ·t/M ≥ 1, and is an S-claim
`SC ℓ c d M (t/M) (d·(t − M)/M) (φ·t/M)`. -/
def TabOK (ℓ : ℝ → ℝ → ℝ) (cq : ℚ) (d M : ℕ) (tab : List (ℕ × ℚ)) : Prop :=
  ∀ (r tr : ℕ) (φ : ℚ), tab[r]? = some (tr, φ) →
    M < tr ∧ d * (tr - M) ≤ M ∧ 1 ≤ (φ : ℝ) * ((tr : ℝ) / M) ∧
    SC ℓ (cq : ℝ) (d : ℝ) (M : ℝ) ((tr : ℝ) / M) ((d : ℝ) * ((tr : ℝ) - M) / M) ((φ : ℝ) * ((tr : ℝ) / M))

/-- For c ≥ 1, d ≥ 1, M ≥ 1 and a table with `TabOK`: if `tval` returns v at α, then
`TC ℓ c d M α v`. -/
theorem tval_sound (hc : 1 ≤ (cq : ℝ)) (hd : 1 ≤ d) (hM : 1 ≤ M) {tab : List (ℕ × ℚ)}
    (htab : TabOK ℓ cq d M tab) {r : ℕ} {α v : ℚ} (h : tval M tab r α = some v) :
    TC ℓ (cq : ℝ) (d : ℝ) (M : ℝ) (α : ℝ) (v : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  unfold tval at h
  split_ifs at h with hr
  · simp only [Option.some.injEq] at h
    subst h
    push_cast
    exact TC_pop hc hM0.le
  · split at h
    · exact absurd h (by simp)
    · rename_i tr φ heq
      split_ifs at h with hα
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := htab (r - 1) tr φ heq
      have htr : (M : ℝ) < tr := by exact_mod_cast h1
      have hκ : 1 ≤ (tr : ℝ) / M := by rw [le_div_iff₀ hM0]; linarith
      have hε : 0 < (d : ℝ) * ((tr : ℝ) - M) / M := by
        apply div_pos _ hM0
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith
      have hα' : (tr : ℝ) / M ≤ (α : ℝ) := by
        have h' : (((tr : ℚ) / M : ℚ) : ℝ) ≤ (α : ℝ) := Rat.cast_le.mpr hα
        push_cast at h'; exact h'
      have hd0 : (0 : ℝ) < d := by
        have h : (1 : ℝ) ≤ d := (by exact_mod_cast hd)
        linarith
      have hdε : (d : ℝ) * ((tr : ℝ) / M - 1) ≤ (d : ℝ) * ((tr : ℝ) - M) / M :=
        le_of_eq (by field_simp)
      have hd1r : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hε1r : (d : ℝ) * ((tr : ℝ) - M) / M ≤ 1 := by
        rw [div_le_one hM0]
        have h2' : ((d * (tr - M) : ℕ) : ℝ) ≤ M := by exact_mod_cast h2
        rw [Nat.cast_mul, Nat.cast_sub h1.le] at h2'
        exact h2'
      have := TC_of_SC hM0.le hd1r hκ hε hε1r hdε h4 hα'
      have e : (φ : ℝ) * ((tr : ℝ) / M) / ((tr : ℝ) / M) * (α : ℝ) = ((φ * α : ℚ) : ℝ) := by
        have : (tr : ℝ) ≠ 0 := by linarith
        push_cast; field_simp
      rw [e] at this; exact this

/-- For c ≥ 1, d ≥ 1, M ≥ 1, a table with `TabOK` and i ≤ M: if `chain` returns W from
position j, then W ≥ 1 and `SC ℓ c d M (j/M) (i/M) W`. -/
theorem chain_sound (hℓ : LogOK ℓ) (hc : 1 ≤ (cq : ℝ)) (hd : 1 ≤ d) (hM : 1 ≤ M) {tab : List (ℕ × ℚ)}
    (htab : TabOK ℓ cq d M tab) {i p : ℕ} (hi : i ≤ M) :
    ∀ (steps : List (ℕ × ℕ × ℕ)) (j : ℕ) (W : ℚ), chain cq M i p SH tab j steps = some W →
      1 ≤ (W : ℝ) ∧ SC ℓ (cq : ℝ) (d : ℝ) (M : ℝ) ((j : ℝ) / M) ((i : ℝ) / M) (W : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  intro steps
  induction steps with
  | nil =>
    intro j W h
    simp only [chain] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    push_cast
    exact ⟨le_max_left _ _, SC_pop hc hM0.le⟩
  | cons st rest ih =>
    intro j W h
    obtain ⟨ku, r, w⟩ := st
    simp only [chain] at h
    split_ifs at h with hcond
    obtain ⟨h1, h2, h3, h4⟩ := hcond
    split at h
    · exact absurd h (by simp)
    rename_i W' hW'
    obtain ⟨hW'1, hW'sc⟩ := ih _ _ hW'
    split at h
    · exact absurd h (by simp)
    rename_i v hv
    split_ifs at h with hv'
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hv1, hv2⟩ := hv'
    have hT := tval_sound hc hd hM htab hv
    have hku : (M : ℝ) ≤ ku := by exact_mod_cast h1
    have hu : (1 : ℝ) ≤ (ku : ℝ) / M := by rw [le_div_iff₀ hM0]; linarith
    have hu0 : (0 : ℝ) < (ku : ℝ) / M := by linarith
    have hsub : ((j + i - ku : ℕ) : ℝ) = (j : ℝ) + i - ku := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hSC := SC_speed (c := (cq : ℝ)) (d := (d : ℝ)) hℓ hc (κ := (j : ℝ) / M) hM0.le hW'sc hT hu
      (by rw [div_le_div_iff_of_pos_right hM0]; exact_mod_cast h2)
      (by rw [hsub]; field_simp)
      (by rw [hsub, div_le_div_iff_of_pos_right hM0]; have : (ku : ℝ) ≤ j := by exact_mod_cast h3
          linarith)
      (by rw [le_div_iff₀ hM0, one_mul]; exact_mod_cast h4)
      (by rw [div_le_one hM0]; exact_mod_cast hi)
      (div_nonneg (Nat.cast_nonneg _) hM0.le)
      (by
        rw [div_mul_cancel₀ _ hM0.ne']
        have h5 : (M : ℝ) ≤ ((j + i - ku : ℕ) : ℝ) := by exact_mod_cast h4
        have h6 : (1 : ℝ) ≤ M := by exact_mod_cast hM
        linarith)
      (by
        have e : ((ku : ℝ) / M) * max 1 ((W' : ℝ) / ((ku : ℝ) / M)) = max ((ku : ℝ) / M) (W' : ℝ) := by
          rw [mul_max_of_nonneg _ _ hu0.le, mul_one, mul_div_cancel₀ _ hu0.ne']
        push_cast
        rw [mul_assoc, mul_comm (max (1 : ℝ) _), e])
      (by
        have h' : ((1 : ℚ) : ℝ) ≤ (((ku : ℚ) / M * v : ℚ) : ℝ) := Rat.cast_le.mpr hv1
        push_cast at h'; exact h')
    have h1' : ((1 : ℚ) : ℝ) ≤ (((ku : ℚ) / M * v : ℚ) : ℝ) := Rat.cast_le.mpr hv1
    have h2' : (((ku : ℚ) / M * v : ℚ) : ℝ) ≤ (((w : ℚ) / 2 ^ SH : ℚ) : ℝ) := Rat.cast_le.mpr hv2
    push_cast at h1' h2' ⊢
    refine ⟨by linarith, SC_mono hM0.le (by linarith) h2' hSC⟩

/-- For c ≥ 1, d ≥ 1 and M ≥ 1, `procNodes` preserves `TabOK`. -/
theorem procNodes_sound (hℓ : LogOK ℓ) (hc : 1 ≤ (cq : ℝ)) (hd : 1 ≤ d) (hM : 1 ≤ M) :
    ∀ (nodes : List Node) (tab tab' : List (ℕ × ℚ)), TabOK ℓ cq d M tab →
      procNodes cq d M SH tab nodes = some tab' → TabOK ℓ cq d M tab' := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  intro nodes
  induction nodes with
  | nil => intro tab tab' h e; simp only [procNodes, Option.some.injEq] at e; subst e; exact h
  | cons nd rest ih =>
    intro tab tab' htab e
    simp only [procNodes] at e
    split_ifs at e with hcond
    obtain ⟨h1, h2⟩ := hcond
    split at e
    · exact absurd e (by simp)
    rename_i W hW
    split_ifs at e with hφ
    obtain ⟨hφ1, hφ2⟩ := hφ
    apply ih _ _ _ e
    obtain ⟨hW1, hSC⟩ := chain_sound (SH := SH) hℓ hc hd hM htab h2 nd.steps nd.t W hW
    intro r tr φ hr
    rcases lt_or_ge r tab.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hr
      exact htab r tr φ hr
    · rw [List.getElem?_append_right hge] at hr
      have hlt1 : r - tab.length < [(nd.t, (nd.phi : ℚ) / 2 ^ SH)].length := by
        by_contra hcon
        push Not at hcon
        rw [List.getElem?_eq_none hcon] at hr
        exact absurd hr (by simp)
      have : r - tab.length = 0 := by simpa using hlt1
      rw [this] at hr
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hφ2' : ((1 : ℚ) : ℝ) ≤ (((nd.phi : ℚ) / 2 ^ SH * ((nd.t : ℚ) / M) : ℚ) : ℝ) :=
        Rat.cast_le.mpr hφ2
      push_cast at hφ2'
      refine ⟨h1, h2, by push_cast; exact hφ2', ?_⟩
      have hκ : (0 : ℝ) < (nd.t : ℝ) / M := by
        apply div_pos _ hM0; have : (M : ℝ) < nd.t := by exact_mod_cast h1
        linarith
      have hε : ((d * (nd.t - M) : ℕ) : ℝ) / M = (d : ℝ) * ((nd.t : ℝ) - M) / M := by
        rw [Nat.cast_mul, Nat.cast_sub h1.le]
      rw [← hε]
      refine SC_mono hM0.le (by linarith) ?_ hSC
      have : ((W / ((nd.t : ℚ) / M) : ℚ) : ℝ) ≤ (((nd.phi : ℚ) / 2 ^ SH : ℚ) : ℝ) := by exact_mod_cast hφ1
      push_cast at this ⊢
      rwa [div_le_iff₀ hκ] at this

/-- For every log n output `ℓ` with `LogOK ℓ`: if `dagCheck c d M SH nodes root = true` then there
is a strict normal-form proof `HY.NFO ℓ c d Mp n` (c and d cast to ℝ) with kernel time ≥ input
superscript and `SpOK` on every line `Mp i`, i ≤ n. -/
theorem dagCheck_soundO (hℓ : LogOK ℓ) {nodes : List Node} {root : ℕ}
    (h : dagCheck cq d M SH nodes root = true) :
    ∃ Mp n, HY.NFO ℓ (cq : ℝ) (d : ℝ) Mp n ∧
      ∀ i ≤ n, pin (Mp i).1 ≤ (Mp i).2.time ∧ SpOK (Mp i).2 := by
  simp only [dagCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, hd⟩, hM⟩, h⟩ := h
  have hc' : (1 : ℝ) ≤ cq := by exact_mod_cast hc
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  split at h
  · exact absurd h (by simp)
  rename_i tab htab
  split at h
  · exact absurd h (by simp)
  rename_i tr φ hr
  have hcφ : cq * φ < 1 := by simpa using h
  have hok := procNodes_sound (SH := SH) hℓ hc' hd hM nodes [] tab (by intro r tr φ h; simp at h) htab
  obtain ⟨h1, h2, h3, h4⟩ := hok root tr φ hr
  have htr : (M : ℝ) < tr := by exact_mod_cast h1
  have hκ : 1 < (tr : ℝ) / M := by rw [lt_div_iff₀ hM0]; linarith
  have hε1r : (d : ℝ) * ((tr : ℝ) - M) / M ≤ 1 := by
    rw [div_le_one hM0]
    have h2' : ((d * (tr - M) : ℕ) : ℝ) ≤ M := by exact_mod_cast h2
    rw [Nat.cast_mul, Nat.cast_sub h1.le] at h2'
    exact h2'
  refine nf_of_SC hc' hM0.le (by positivity) hκ ?_ hε1r h3 ?_ h4
  · rw [mul_sub, mul_one, mul_div_assoc]; apply le_of_eq; field_simp
  · have : ((cq * φ : ℚ) : ℝ) < 1 := by exact_mod_cast hcφ
    push_cast at this
    have hκ0 : (0 : ℝ) < (tr : ℝ) / M := by linarith
    calc (cq : ℝ) * ((φ : ℝ) * ((tr : ℝ) / M)) = ((cq : ℝ) * φ) * ((tr : ℝ) / M) := by ring
      _ < 1 * ((tr : ℝ) / M) := mul_lt_mul_of_pos_right this hκ0
      _ = (tr : ℝ) / M := one_mul _

/-- If `dagCheck c d M SH nodes root = true` then there is a strict normal-form proof
`HY.NF c d Mp n` (c and d cast to ℝ) with kernel time ≥ input superscript and `SpOK` on every line
`Mp i`, i ≤ n. -/
theorem dagCheck_sound {nodes : List Node} {root : ℕ} (h : dagCheck cq d M SH nodes root = true) :
    ∃ Mp n, HY.NF (cq : ℝ) (d : ℝ) Mp n ∧ ∀ i ≤ n, pin (Mp i).1 ≤ (Mp i).2.time ∧ SpOK (Mp i).2 :=
  let ⟨Mp, n, h, h'⟩ := dagCheck_soundO logOK_max h
  ⟨Mp, n, nf_of_nfO_max h, h'⟩

/-- If `dagCheck c d M SH nodes root = true` then there is a strict normal-form proof
`HY.NFO (fun _ _ => 1) c d Mp n`, in the calculus in which the new log n block of Lemma 3.3 has
output exactly 1, with kernel time ≥ input superscript and `SpOK` on every line `Mp i`, i ≤ n. -/
theorem dagCheck_sound1 {nodes : List Node} {root : ℕ} (h : dagCheck cq d M SH nodes root = true) :
    ∃ Mp n, HY.NFO (fun _ _ => 1) (cq : ℝ) (d : ℝ) Mp n ∧
      ∀ i ≤ n, pin (Mp i).1 ≤ (Mp i).2.time ∧ SpOK (Mp i).2 :=
  dagCheck_soundO logOK_one h

end sound

end HDS
end PastaMath.OneTapeThreshold
