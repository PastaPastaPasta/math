import PastaMath.TautThreshold.Basic

/-!
# The reduced TAUT-versus-NTS calculus and its limit

A homogeneous relaxation `TStep` of the alternation-trading calculus of R. Williams,
"Alternation-trading proofs, linear programming, and lower bounds" (ACM TOCT 2013, §6:
Lemma 6.1 speedup, Lemma 6.2 slowdown, Definition 6.4 normal form), and its limit
`no_trefutation`: no normal-form refutation `TRefutes c n L` exists for any c with c³ ≥ 4.
The connection to the calculus in Williams's own line format is made in `Literal.lean`.

A line is (sups, matching, a): the input constraints of the quantifier blocks (outermost
first), whether the kernel's type matches the innermost block (NTS under ∃, coNTS under ∀),
and the kernel exponent. Potential: `Ps c b a = min (max b a) (max (c/2 · a) (5/2 · b))` on
matching lines, `Ps c b (c · Ps c b a)` on opposite lines.
-/

namespace PastaMath.TautThreshold
namespace TL

noncomputable def Ps (c b a : ℝ) : ℝ := min (max b a) (max (c / 2 * a) (5 / 2 * b))

theorem ps_mono {c b a b' a' : ℝ} (hc : 0 ≤ c) (hb : b ≤ b') (ha : a ≤ a') :
    Ps c b a ≤ Ps c b' a' := by
  unfold Ps
  apply min_le_min (max_le_max hb ha)
  apply max_le_max <;> nlinarith

theorem ps_le_max {c b a : ℝ} : Ps c b a ≤ max b a := min_le_left _ _

theorem ps_ge_g {c b a : ℝ} (_hc : 0 ≤ c) (hc2 : c ≤ 2) (ha : 0 ≤ a) : c / 2 * a ≤ Ps c b a := by
  unfold Ps
  apply le_min
  · exact le_trans (by nlinarith) (le_max_right b a)
  · exact le_max_left _ _

theorem ps_ge_min {c b a : ℝ} : min a (5 / 2 * b) ≤ Ps c b a := by
  unfold Ps
  apply le_min
  · exact le_trans (min_le_left _ _) (le_max_right _ _)
  · exact le_trans (min_le_right _ _) (le_max_right _ _)

theorem ps_ge_b {c b a : ℝ} (hb : 0 ≤ b) (_hab : a ≤ b) : b ≤ Ps c b a := by
  unfold Ps
  apply le_min (le_max_left _ _)
  exact le_trans (by linarith) (le_max_right _ _)

theorem ps_nonneg {c b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) : 0 ≤ Ps c b a := by
  unfold Ps
  exact le_min (le_trans ha (le_max_right _ _)) (le_trans (by linarith) (le_max_right _ _))

/-- Facts about c ∈ [∛4, 2] used below. -/
theorem cfacts {c : ℝ} (hc3 : 4 ≤ c ^ 3) (hc2 : c ≤ 2) :
    3 / 2 ≤ c ∧ 5 / 2 ≤ c ^ 2 ∧ 1 ≤ c - c ^ 2 / 5 ∧ c ≤ c ^ 4 / 4 ∧ 1 ≤ c ^ 3 / 4 := by
  have h1 : 3 / 2 ≤ c := by
    by_contra h; push Not at h
    have h0 : 0 ≤ c := by
      by_contra h'; push Not at h'; nlinarith [sq_nonneg c]
    nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
  have h2 : 5 / 2 ≤ c ^ 2 := by
    by_contra h; push Not at h
    nlinarith
  refine ⟨h1, h2, by nlinarith, by nlinarith, by nlinarith⟩

section leaves
variable {c a b x D E W P h T : ℝ}

theorem leaf_A1a (hc0 : 0 ≤ c) (hWcb : c * b ≤ W) (hEW : c * W ≤ E) (hh : h ≤ c ^ 2 * b) :
    h ≤ E := by
  have := mul_le_mul_of_nonneg_left hWcb hc0
  nlinarith

theorem leaf_A1b (hc1 : 1 ≤ c) (hb : 0 ≤ b) (hgt : c ^ 2 * b < h) (hga : h ≤ c / 2 * a)
    (hD : a - x ≤ b) (hEx : c * x ≤ E) : h ≤ E := by
  have hcb : c * b < a / 2 := by
    by_contra hc; push Not at hc
    have : c * (a / 2) ≤ c * (c * b) := mul_le_mul_of_nonneg_left hc (by linarith)
    nlinarith
  have : c * (a - b) ≤ c * x := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have ha : 0 ≤ a := by nlinarith
  nlinarith

theorem leaf_A2i (hc1 : 1 ≤ c) (hc34 : 1 ≤ c ^ 3 / 4) (hD0 : 0 ≤ D) (hDa : D = a - x)
    (hWD : c ^ 3 / 4 * D ≤ W) (hEW : c * W ≤ E) (hEx : c * x ≤ E) (hga : h ≤ c / 2 * a) :
    h ≤ E := by
  have h1 : D ≤ W := by nlinarith
  have h2 : c * D ≤ c * W := mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3 : c * D + c * x = c * a := by rw [hDa]; ring
  nlinarith

theorem leaf_A2ii (hc0 : 0 ≤ c) (hcsq : 5 / 2 ≤ c ^ 2) (_hc1 : 1 ≤ c) (hb : 0 ≤ b)
    (hkb : h ≤ 5 / 2 * b) (hbD : b < D) (hEW : c * W ≤ E)
    (hW : min (c * P) (5 / 2 * b) ≤ W) (hP : min D (5 / 2 * b) ≤ P) : h ≤ E := by
  rcases le_total (c * P) (5 / 2 * b) with hm | hm
  · rw [min_eq_left hm] at hW
    rcases le_total D (5 / 2 * b) with hm2 | hm2
    · rw [min_eq_left hm2] at hP
      have h1 : c * D ≤ c * P := mul_le_mul_of_nonneg_left hP hc0
      have h2 : c * (c * D) ≤ c * W := mul_le_mul_of_nonneg_left (le_trans h1 hW) hc0
      have h3 : c * (c * D) = c ^ 2 * D := by ring
      have h4 : 5 / 2 * D ≤ c ^ 2 * D := mul_le_mul_of_nonneg_right hcsq (by linarith)
      linarith
    · rw [min_eq_right hm2] at hP
      have h1 : c * (5 / 2 * b) ≤ c * P := mul_le_mul_of_nonneg_left hP hc0
      have h2 : 5 / 2 * b ≤ c * (5 / 2 * b) := by nlinarith
      have h3 : c * (c * P) ≤ c * W := mul_le_mul_of_nonneg_left hW hc0
      have h4 : c * P ≤ c * (c * P) := by nlinarith [mul_nonneg hc0 hb]
      linarith
  · rw [min_eq_right hm] at hW
    have h1 : c * (5 / 2 * b) ≤ c * W := mul_le_mul_of_nonneg_left hW hc0
    have h2 : 5 / 2 * b ≤ c * (5 / 2 * b) := by nlinarith
    linarith

theorem leaf_B (hc0 : 0 ≤ c) (hc5 : 1 ≤ c - c ^ 2 / 5) (hc4 : c ≤ c ^ 4 / 4) (hD0 : 0 ≤ D)
    (hx : 0 ≤ x)
    (hDa : D = a - x) (hWD : c ^ 3 / 4 * D ≤ W) (hEW : c * W ≤ E) (hkx : 5 / 2 * x < h)
    (hga : h ≤ c / 2 * a) : c / 2 * a ≤ c / 2 * E := by
  have h1 : c * (c ^ 3 / 4 * D) ≤ c * W := mul_le_mul_of_nonneg_left hWD hc0
  have h1' : c * (c ^ 3 / 4 * D) = c ^ 4 / 4 * D := by ring
  have h2 : c * D ≤ c ^ 4 / 4 * D := mul_le_mul_of_nonneg_right hc4 hD0
  have hxa : x < c / 5 * a := by
    have e : c / 5 * a = 2 / 5 * (c / 2 * a) := by ring
    rw [e]; linarith
  have h3 : c * x ≤ c * (c / 5 * a) := mul_le_mul_of_nonneg_left hxa.le hc0
  have h3' : c * (c / 5 * a) = c ^ 2 / 5 * a := by ring
  have ha : 0 ≤ a := by linarith
  have h4 : 1 * a ≤ (c - c ^ 2 / 5) * a := mul_le_mul_of_nonneg_right hc5 ha
  have h4' : (c - c ^ 2 / 5) * a = c * a - c ^ 2 / 5 * a := by ring
  have h5 : c * D = c * a - c * x := by rw [hDa]; ring
  have h6 : a ≤ E := by linarith
  exact mul_le_mul_of_nonneg_left h6 (by linarith)

end leaves

/-- The step inequality. `T` is the merged parent superscript, `E` the cost of popping the index
block, whose inner level started from (b, a − x) with an opposite-type kernel. -/
theorem key {c b a x T E : ℝ} (hc3 : 4 ≤ c ^ 3) (hc2 : c ≤ 2) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hxa : x ≤ a) (hT1 : x ≤ T) (hT2 : b ≤ T)
    (hE : c * max T (Ps c b (c * Ps c b (a - x))) ≤ E) : Ps c b a ≤ Ps c T E := by
  obtain ⟨hc15, hcsq, hc5, hc4, hc34⟩ := cfacts hc3 hc2
  have hc0 : 0 ≤ c := by linarith
  have hc1 : 1 ≤ c := by linarith
  obtain ⟨D, hDa⟩ : ∃ D, D = a - x := ⟨_, rfl⟩
  rw [← hDa] at hE
  have hD0 : 0 ≤ D := by linarith
  obtain ⟨P, hPd⟩ : ∃ P, P = Ps c b D := ⟨_, rfl⟩
  obtain ⟨W, hWd⟩ : ∃ W, W = Ps c b (c * P) := ⟨_, rfl⟩
  rw [← hPd, ← hWd] at hE
  have hP0 : 0 ≤ P := hPd ▸ ps_nonneg hb hD0
  have hET : c * T ≤ E := le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hc0) hE
  have hEW : c * W ≤ E := le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hc0) hE
  have hEx : c * x ≤ E := le_trans (mul_le_mul_of_nonneg_left hT1 hc0) hET
  obtain ⟨h, hhd⟩ : ∃ h, h = Ps c b a := ⟨_, rfl⟩
  rw [← hhd]
  have hh1 : h ≤ max b a := hhd ▸ ps_le_max
  have hh2 : h ≤ max (c / 2 * a) (5 / 2 * b) := hhd ▸ min_le_right _ _
  have hPg : c / 2 * D ≤ P := hPd ▸ ps_ge_g hc0 hc2 hD0
  have hWg : c / 2 * (c * P) ≤ W := hWd ▸ ps_ge_g hc0 hc2 (mul_nonneg hc0 hP0)
  have hPm : min D (5 / 2 * b) ≤ P := hPd ▸ ps_ge_min
  have hWm : min (c * P) (5 / 2 * b) ≤ W := hWd ▸ ps_ge_min
  have hWD : c ^ 3 / 4 * D ≤ W := by
    have e1 : c / 2 * (c * (c / 2 * D)) ≤ c / 2 * (c * P) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPg hc0) (by linarith)
    have e2 : c / 2 * (c * (c / 2 * D)) = c ^ 3 / 4 * D := by ring
    linarith
  have hm2 : h ≤ c / 2 * a ∨ h ≤ 5 / 2 * b := by
    rcases le_total (c / 2 * a) (5 / 2 * b) with hm | hm
    · rw [max_eq_right hm] at hh2; exact Or.inr hh2
    · rw [max_eq_left hm] at hh2; exact Or.inl hh2
  have hkc : 5 / 2 * b ≤ c ^ 2 * b := mul_le_mul_of_nonneg_right hcsq hb
  have hA : h ≤ E := by
    rcases le_or_gt h (c * T) with hcT | hcT
    · exact le_trans hcT hET
    have hcb : c * b < h := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hT2 hc0) hcT
    rcases le_or_gt D b with hbD | hbD
    · have hPb : b ≤ P := hPd ▸ ps_ge_b hb hbD
      have hWcb : c * b ≤ W :=
        le_trans (le_min (mul_le_mul_of_nonneg_left hPb hc0) (by nlinarith)) hWm
      rcases le_or_gt h (c ^ 2 * b) with h1 | h1
      · exact leaf_A1a hc0 hWcb hEW h1
      · have hga : h ≤ c / 2 * a := by
          rcases hm2 with h' | h'
          · exact h'
          · linarith
        exact leaf_A1b hc1 hb h1 hga (by linarith) hEx
    · rcases hm2 with hga | hkb
      · exact leaf_A2i hc1 hc34 hD0 hDa hWD hEW hEx hga
      · exact leaf_A2ii hc0 hcsq hc1 hb hkb hbD hEW hWm hPm
  have hB : h ≤ max (c / 2 * E) (5 / 2 * T) := by
    rcases le_or_gt h (5 / 2 * T) with hkT | hkT
    · exact le_trans hkT (le_max_right _ _)
    have hkx : 5 / 2 * x < h := lt_of_le_of_lt (by linarith) hkT
    have hkb : 5 / 2 * b < h := lt_of_le_of_lt (by linarith) hkT
    have hga : h ≤ c / 2 * a := by
      rcases hm2 with h' | h'
      · exact h'
      · linarith
    exact le_trans (le_trans hga (leaf_B hc0 hc5 hc4 hD0 hx hDa hWD hEW hkx hga)) (le_max_left _ _)
  unfold Ps
  exact le_min (le_trans hA (le_max_right _ _)) hB

/-! ### The calculus -/

abbrev TLine := List ℝ × Bool × ℝ

/-- Reduced TAUT-vs-NTS rules. `true` = kernel type matches the last block. `speedM` merges the
guessed configurations into the last block and opens an index block of the other quantifier
(W13 Lemma 6.1 when the kernel matches); `speedO` opens a configuration block and an index block
(Lemma 6.1 when it does not); `flip` applies H to the kernel alone (Lemma 6.2(3),(4), and the
converse direction, also sound); `pop` removes the last block with its matching kernel
(Lemma 6.2(1),(2)); `weak` is weakening. With x = 0, `speedM`/`speedO` are dummy blocks. -/
inductive TStep (c : ℝ) : TLine → TLine → Prop
  | init (a : ℝ) : TStep c ([], true, a) ([0], true, a)
  | speedM (bs : List ℝ) (b a x b₁ b₂ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a) (h₁ : max x b ≤ b₁)
      (h₂ : b ≤ b₂) (h₃ : a - x ≤ a₂) : TStep c (bs ++ [b], true, a) (bs ++ [b₁, b₂], false, a₂)
  | speedO (bs : List ℝ) (b a x b₁ b₂ a₂ : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a) (h₁ : max x b ≤ b₁)
      (h₂ : b ≤ b₂) (h₃ : a - x ≤ a₂) :
      TStep c (bs ++ [b], false, a) (bs ++ [b, b₁, b₂], false, a₂)
  | flip (bs : List ℝ) (b a e : ℝ) (t : Bool) (h : c * max b a ≤ e) :
      TStep c (bs ++ [b], t, a) (bs ++ [b], !t, e)
  | pop (bs : List ℝ) (b a e : ℝ) (h : c * max (top bs) (max b a) ≤ e) :
      TStep c (bs ++ [b], true, a) (bs, true, e)
  | weak (bs bs' : List ℝ) (t : Bool) (a a' : ℝ) (hl : bs'.length = bs.length)
      (hle : ∀ i, bs.getD i 0 ≤ bs'.getD i 0) (ha : a ≤ a') : TStep c (bs, t, a) (bs', t, a')

/-- A normal-form proof NTS[n^a] ⊆ … ⊆ coNTS[n^{a'}] with a' ≤ a (W13 Definition 6.4 and
Lemma 6.5 accept a' = a), at least two steps, and no quantifier-free intermediate line. -/
def TRefutes (c : ℝ) (n : ℕ) (L : ℕ → TLine) : Prop :=
  2 ≤ n ∧ (L 0).1 = [] ∧ (L n).1 = [] ∧ 0 < (L 0).2.2 ∧ (L n).2.2 ≤ (L 0).2.2 ∧
    (∀ i < n, TStep c (L i) (L (i + 1))) ∧ (∀ i, 0 < i → i < n → (L i).1 ≠ [])

noncomputable def pot (c : ℝ) (L : TLine) : ℝ :=
  if L.2.1 then Ps c (top L.1) L.2.2 else Ps c (top L.1) (c * Ps c (top L.1) L.2.2)

def NN (L : TLine) : Prop := (∀ i, 0 ≤ L.1.getD i 0) ∧ 0 ≤ L.2.2

theorem tstep_inv {c : ℝ} {L L' : TLine} (h : TStep c L L') :
    (L.1 = [] ∧ L'.1 = [0] ∧ L'.2.1 = true ∧ L'.2.2 = L.2.2) ∨
    (∃ (bs : List ℝ) (b x b₁ b₂ : ℝ), 0 ≤ x ∧ x ≤ L.2.2 ∧ max x b ≤ b₁ ∧ b ≤ b₂ ∧
      L.2.2 - x ≤ L'.2.2 ∧ L.1 = bs ++ [b] ∧ L.2.1 = true ∧ L'.1 = bs ++ [b₁, b₂] ∧
      L'.2.1 = false) ∨
    (∃ (bs : List ℝ) (b x b₁ b₂ : ℝ), 0 ≤ x ∧ x ≤ L.2.2 ∧ max x b ≤ b₁ ∧ b ≤ b₂ ∧
      L.2.2 - x ≤ L'.2.2 ∧ L.1 = bs ++ [b] ∧ L.2.1 = false ∧ L'.1 = bs ++ [b, b₁, b₂] ∧
      L'.2.1 = false) ∨
    (∃ (bs : List ℝ) (b : ℝ), L.1 = bs ++ [b] ∧ L'.1 = bs ++ [b] ∧ L'.2.1 = !L.2.1 ∧
      c * max b L.2.2 ≤ L'.2.2) ∨
    (∃ (bs : List ℝ) (b : ℝ), L.1 = bs ++ [b] ∧ L.2.1 = true ∧ L'.1 = bs ∧ L'.2.1 = true ∧
      c * max (top bs) (max b L.2.2) ≤ L'.2.2) ∨
    (L'.1.length = L.1.length ∧ (∀ i, L.1.getD i 0 ≤ L'.1.getD i 0) ∧ L'.2.1 = L.2.1 ∧
      L.2.2 ≤ L'.2.2) := by
  cases h with
  | init a => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | speedM bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact Or.inr (Or.inl ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, rfl, rfl, rfl, rfl⟩)
  | speedO bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ =>
    exact Or.inr (Or.inr (Or.inl ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, rfl, rfl, rfl, rfl⟩))
  | flip bs b a e t h => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨bs, b, rfl, rfl, rfl, h⟩)))
  | pop bs b a e h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨bs, b, rfl, rfl, rfl, rfl, h⟩))))
  | weak bs bs' t a a' hl hle ha => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hl, hle, rfl, ha⟩))))

theorem getD_snoc_len (bs : List ℝ) (b : ℝ) : (bs ++ [b]).getD bs.length 0 = b := by
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl

theorem getD_lt {bs l : List ℝ} {i : ℕ} (h : i < bs.length) : (bs ++ l).getD i 0 = bs.getD i 0 :=
  List.getD_append _ _ _ _ h

theorem nn_app {bs l : List ℝ} (h1 : ∀ i, i < bs.length → 0 ≤ bs.getD i 0)
    (h2 : ∀ j, 0 ≤ l.getD j 0) : ∀ i, 0 ≤ (bs ++ l).getD i 0 := by
  intro i
  rcases lt_or_ge i bs.length with hi | hi
  · rw [getD_lt hi]; exact h1 i hi
  · rw [List.getD_append_right _ _ _ _ hi]; exact h2 _

theorem nn_pref {bs l : List ℝ} (h : ∀ i, 0 ≤ (bs ++ l).getD i 0) :
    ∀ i, i < bs.length → 0 ≤ bs.getD i 0 := by
  intro i hi; have := h i; rwa [getD_lt hi] at this

theorem getD2_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : ∀ j, 0 ≤ [u, v].getD j 0 := by
  intro j; rcases j with _ | _ | j <;> simp [hu, hv]

theorem getD3_nonneg {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    ∀ j, 0 ≤ [u, v, w].getD j 0 := by
  intro j; rcases j with _ | _ | _ | j <;> simp [hu, hv, hw]

theorem getD1_nonneg {u : ℝ} (hu : 0 ≤ u) : ∀ j, 0 ≤ [u].getD j 0 := by
  intro j; rcases j with _ | j <;> simp [hu]

theorem top_nonneg {l : List ℝ} (h : ∀ i, 0 ≤ l.getD i 0) : 0 ≤ top l := h _

theorem tstep_nonneg {c : ℝ} (hc : 0 ≤ c) {L L' : TLine} (h : TStep c L L') (hL : NN L) :
    NN L' := by
  obtain ⟨hL1, hL2⟩ := hL
  rcases tstep_inv h with ⟨-, e1, -, e2⟩ | ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, e0, -, e1, -⟩ |
    ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, e0, -, e1, -⟩ | ⟨bs, b, e0, e1, -, hf⟩ |
    ⟨bs, b, e0, -, e1, -, hf⟩ | ⟨hl, hle, -, ha⟩
  · refine ⟨?_, by rw [e2]; exact hL2⟩
    rw [e1]; exact getD1_nonneg le_rfl
  · rw [e0] at hL1
    have hb : 0 ≤ b := by have := hL1 bs.length; rwa [getD_snoc_len] at this
    refine ⟨?_, by linarith⟩
    rw [e1]
    exact nn_app (nn_pref hL1) (getD2_nonneg (le_trans hb (le_trans (le_max_right _ _) h₁))
      (le_trans hb h₂))
  · rw [e0] at hL1
    have hb : 0 ≤ b := by have := hL1 bs.length; rwa [getD_snoc_len] at this
    refine ⟨?_, by linarith⟩
    rw [e1]
    exact nn_app (nn_pref hL1) (getD3_nonneg hb (le_trans hb (le_trans (le_max_right _ _) h₁))
      (le_trans hb h₂))
  · have hb : 0 ≤ b := by have := hL1 bs.length; rwa [e0, getD_snoc_len] at this
    refine ⟨by rw [e1, ← e0]; exact hL1, ?_⟩
    exact le_trans (mul_nonneg hc (le_trans hb (le_max_left _ _))) hf
  · rw [e0] at hL1
    have hb : 0 ≤ b := by have := hL1 bs.length; rwa [getD_snoc_len] at this
    refine ⟨?_, le_trans (mul_nonneg hc (le_trans (le_trans hb (le_max_left _ _))
      (le_max_right _ _))) hf⟩
    rw [e1]; intro i
    rcases lt_or_ge i bs.length with hi | hi
    · exact nn_pref hL1 i hi
    · rw [List.getD_eq_default _ _ hi]
  · exact ⟨fun i => le_trans (hL1 i) (hle i), le_trans hL2 ha⟩

theorem tstep_restrict {c c₀ : ℝ} (hcc : c₀ ≤ c) {L L' : TLine} (h : TStep c L L') (hL : NN L) :
    TStep c₀ L L' := by
  obtain ⟨hL1, hL2⟩ := hL
  cases h with
  | init a => exact TStep.init a
  | speedM bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ => exact TStep.speedM bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃
  | speedO bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃ => exact TStep.speedO bs b a x b₁ b₂ a₂ hx hxa h₁ h₂ h₃
  | flip bs b a e t hf =>
    have hb : 0 ≤ b := by have := hL1 bs.length; rwa [getD_snoc_len] at this
    exact TStep.flip bs b a e t (le_trans (mul_le_mul_of_nonneg_right hcc
      (le_trans hb (le_max_left _ _))) hf)
  | pop bs b a e hf =>
    have hb : 0 ≤ b := by have := hL1 bs.length; rwa [getD_snoc_len] at this
    exact TStep.pop bs b a e (le_trans (mul_le_mul_of_nonneg_right hcc
      (le_trans (le_trans hb (le_max_left _ _)) (le_max_right _ _))) hf)
  | weak bs bs' t a a' hl hle ha => exact TStep.weak bs bs' t a a' hl hle ha

theorem tstep_len {c : ℝ} {L L' : TLine} (h : TStep c L L') : L.1.length ≤ L'.1.length + 1 := by
  rcases tstep_inv h with ⟨e0, e1, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -, e1, -⟩ |
    ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -, e1, -⟩ | ⟨bs, b, e0, e1, -, -⟩ |
    ⟨bs, b, e0, -, e1, -, -⟩ | ⟨hl, -, -, -⟩
  all_goals first
    | (rw [e0, e1]; simp)
    | omega

theorem tstep_pop {c : ℝ} {L L' : TLine} (h : TStep c L L')
    (hd : L'.1.length + 1 = L.1.length) :
    L.2.1 = true ∧ L'.2.1 = true ∧ L.1 = L'.1 ++ [top L.1] ∧
      c * max (top L'.1) (max (top L.1) L.2.2) ≤ L'.2.2 := by
  rcases tstep_inv h with ⟨e0, e1, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -, e1, -⟩ |
    ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -, e1, -⟩ | ⟨bs, b, e0, e1, -, -⟩ |
    ⟨bs, b, e0, t1, e1, t2, hf⟩ | ⟨hl, -, -, -⟩
  · rw [e0, e1] at hd; simp at hd
  · rw [e0, e1] at hd; simp at hd
  · rw [e0, e1] at hd; simp at hd
  · rw [e0, e1] at hd; simp at hd
  · refine ⟨t1, t2, ?_, ?_⟩
    · rw [e0, e1, top_concat]
    · rw [e0, e1, top_concat]; exact hf
  · omega

theorem tstep_getD_mono {c : ℝ} {L L' : TLine} (h : TStep c L L') {k : ℕ}
    (hk : k + 2 ≤ L.1.length) : L.1.getD k 0 ≤ L'.1.getD k 0 := by
  rcases tstep_inv h with ⟨e0, -, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -, e1, -⟩ |
    ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -, e1, -⟩ | ⟨bs, b, e0, e1, -, -⟩ |
    ⟨bs, b, e0, -, e1, -, -⟩ | ⟨-, hle, -, -⟩
  · rw [e0] at hk; simp at hk
  · rw [e0] at hk ⊢; rw [e1]
    simp only [List.length_append, List.length_singleton] at hk
    rw [getD_lt (by omega), getD_lt (by omega)]
  · rw [e0] at hk ⊢; rw [e1]
    simp only [List.length_append, List.length_singleton] at hk
    rw [getD_lt (by omega), getD_lt (by omega)]
  · rw [e0, e1]
  · rw [e0] at hk ⊢; rw [e1]
    simp only [List.length_append, List.length_singleton] at hk
    rw [getD_lt (by omega)]
  · exact hle k

theorem pot_true {c : ℝ} {L : TLine} (h : L.2.1 = true) : pot c L = Ps c (top L.1) L.2.2 := by
  unfold pot; rw [if_pos h]

theorem pot_false {c : ℝ} {L : TLine} (h : L.2.1 = false) :
    pot c L = Ps c (top L.1) (c * Ps c (top L.1) L.2.2) := by
  unfold pot; rw [if_neg (by rw [h]; simp)]

/-- Entry k is nondecreasing along a stretch whose source lines all have depth ≥ k + 2. -/
theorem entry_mono {c : ℝ} (L : ℕ → TLine) (k : ℕ) :
    ∀ j p, (∀ i, p ≤ i → i < p + j → TStep c (L i) (L (i + 1))) →
      (∀ i, p ≤ i → i < p + j → k + 2 ≤ (L i).1.length) →
      (L p).1.getD k 0 ≤ (L (p + j)).1.getD k 0 := by
  intro j
  induction j with
  | zero => intro p _ _; exact le_rfl
  | succ j ih =>
    intro p hs hd
    have h1 := ih p (fun i h1 h2 => hs i h1 (by omega)) (fun i h1 h2 => hd i h1 (by omega))
    have h2 := tstep_getD_mono (hs (p + j) (by omega) (by omega)) (hd (p + j) (by omega) (by omega))
    rw [show p + (j + 1) = p + j + 1 by omega]
    exact le_trans h1 h2

/-- First index after p whose depth is ≤ k. -/
theorem first_return (L : ℕ → TLine) (p q k : ℕ) (hpq : p < q) (hq : (L q).1.length ≤ k) :
    ∃ m, p < m ∧ m ≤ q ∧ (L m).1.length ≤ k ∧ ∀ i, p < i → i < m → k < (L i).1.length := by
  classical
  have hex : ∃ m, p < m ∧ m ≤ q ∧ (L m).1.length ≤ k := ⟨q, hpq, le_rfl, hq⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1, (Nat.find_spec hex).2.2,
    fun i hi1 hi2 => ?_⟩
  by_contra hcon
  push Not at hcon
  exact Nat.find_min hex hi2 ⟨hi1, by have := (Nat.find_spec hex).2.1; omega, hcon⟩

def SegStmt (c : ℝ) (L : ℕ → TLine) (len p k : ℕ) : Prop :=
  (∀ i, p ≤ i → i < p + len → TStep c (L i) (L (i + 1))) →
    (∀ i, p ≤ i → i ≤ p + len → k + 1 ≤ (L i).1.length ∧ NN (L i)) →
    (L p).1.length = k + 1 → (L (p + len)).1.length = k + 1 → pot c (L p) ≤ pot c (L (p + len))

/-- An excursion that starts at depth k+1 and first returns to depth k ends in a matching line
whose kernel pays c·max(parent sup, potential at the start). -/
theorem excursion {c : ℝ} (hc : 0 ≤ c) (L : ℕ → TLine) (N : ℕ)
    (hseg : ∀ len p k, len < N → SegStmt c L len p k) (p q k : ℕ) (hpq : p < q) (hN : q - 1 - p < N)
    (hs : ∀ i, p ≤ i → i < q → TStep c (L i) (L (i + 1)))
    (hd : ∀ i, p ≤ i → i < q → k + 1 ≤ (L i).1.length ∧ NN (L i))
    (hp : (L p).1.length = k + 1) (hq : (L q).1.length = k) :
    (L q).2.1 = true ∧ c * max (top (L q).1) (pot c (L p)) ≤ (L q).2.2 := by
  have hsq := hs (q - 1) (by omega) (by omega)
  rw [show q - 1 + 1 = q by omega] at hsq
  have hlq1 : (L (q - 1)).1.length = k + 1 := by
    have h1 := (hd (q - 1) (by omega) (by omega)).1
    have h2 := tstep_len hsq
    omega
  obtain ⟨t1, t2, -, hf⟩ := tstep_pop hsq (by omega)
  have hS := hseg (q - 1 - p) (p := p) (k := k) hN (fun i h1 h2 => hs i h1 (by omega))
    (fun i h1 h2 => hd i h1 (by omega)) hp (by rw [show p + (q - 1 - p) = q - 1 by omega]; exact hlq1)
  rw [show p + (q - 1 - p) = q - 1 by omega, pot_true t1] at hS
  refine ⟨t2, le_trans ?_ hf⟩
  apply mul_le_mul_of_nonneg_left _ hc
  exact max_le_max le_rfl (le_trans hS ps_le_max)

theorem top_of_len {l : List ℝ} {k : ℕ} (h : l.length = k + 1) : top l = l.getD k 0 :=
  top_eq_getD h

theorem segment {c : ℝ} (hc3 : 4 ≤ c ^ 3) (hc2 : c ≤ 2) (L : ℕ → TLine) :
    ∀ len p k, SegStmt c L len p k := by
  obtain ⟨hc15, hcsq, -, -, hc34⟩ := cfacts hc3 hc2
  have hc0 : 0 ≤ c := by linarith
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
  intro p k hstep hdep hp hq
  rcases Nat.eq_zero_or_pos len with h0 | hlen
  · subst h0; exact le_rfl
  have hs0 := hstep p le_rfl (by omega)
  have hNNp := (hdep p le_rfl (by omega)).2
  have htopp : top (L p).1 = (L p).1.getD k 0 := top_of_len hp
  rcases tstep_inv hs0 with ⟨e0, -, -⟩ | ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, e0, t0, e1, t1⟩ |
    ⟨bs, b, x, b₁, b₂, hx, hxa, h₁, h₂, h₃, e0, t0, e1, t1⟩ | ⟨bs, b, e0, e1, t1, hf⟩ |
    ⟨bs, b, e0, -, e1, -, -⟩ | ⟨hl, hle, t1, ha⟩
  · rw [e0] at hp; simp at hp
  · -- speedM
    have hbs : bs.length = k := by
      rw [e0] at hp; simp only [List.length_append, List.length_singleton] at hp; omega
    have hl1 : (L (p + 1)).1.length = k + 2 := by
      rw [e1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have hb0 : 0 ≤ b := by
      have := hNNp.1 bs.length; rwa [e0, getD_snoc_len] at this
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ := first_return L (p + 1) (p + len) (k + 1)
      (by by_contra hc'; have : len = 1 := by omega
          subst this; rw [hl1] at hq; omega) (by omega)
    have hmk : (L m).1.length = k + 1 := by
      have := (hdep m (by omega) hm2).1; omega
    have hex := excursion hc0 L len (fun len' p' k' h' => ih len' h' p' k') (p + 1) m (k + 1) hm1
      (by omega) (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => ⟨by
          rcases Nat.eq_or_lt_of_le h1 with h | h
          · rw [← h, hl1]
          · have := hm4 i h h2; omega,
        (hdep i (by omega) (by omega)).2⟩) hl1 hmk
    obtain ⟨tm, hcost⟩ := hex
    have hpot1 : pot c (L (p + 1)) = Ps c b₂ (c * Ps c b₂ (L (p + 1)).2.2) := by
      rw [pot_false t1, e1, show bs ++ [b₁, b₂] = (bs ++ [b₁]) ++ [b₂] by simp, top_concat]
    have hW : Ps c b (c * Ps c b ((L p).2.2 - x)) ≤ pot c (L (p + 1)) := by
      rw [hpot1]
      exact ps_mono hc0 h₂ (mul_le_mul_of_nonneg_left (ps_mono hc0 h₂ h₃) hc0)
    have hent := entry_mono L k (m - (p + 1)) (p + 1)
      (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => by
        rcases Nat.eq_or_lt_of_le h1 with h | h
        · rw [← h, hl1]
        · have := hm4 i h (by omega); omega)
    rw [show p + 1 + (m - (p + 1)) = m by omega] at hent
    have hb1 : (L (p + 1)).1.getD k 0 = b₁ := by
      rw [e1, List.getD_append_right _ _ _ _ (by omega), hbs, Nat.sub_self]; rfl
    have htopm : top (L m).1 = (L m).1.getD k 0 := top_of_len hmk
    have hTm : max x b ≤ top (L m).1 := by rw [htopm]; rw [hb1] at hent; exact le_trans h₁ hent
    have hkey := key (b := b) (a := (L p).2.2) (x := x) (T := top (L m).1) (E := (L m).2.2) hc3 hc2
      hb0 hx hxa (le_trans (le_max_left _ _) hTm) (le_trans (le_max_right _ _) hTm)
      (le_trans (mul_le_mul_of_nonneg_left (max_le_max le_rfl hW) hc0) hcost)
    have hrest := ih (p + len - m) (by omega) m k (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => hdep i (by omega) (by omega)) hmk
      (by rw [show m + (p + len - m) = p + len by omega]; exact hq)
    rw [show m + (p + len - m) = p + len by omega] at hrest
    have hbtop : top (L p).1 = b := by rw [e0, top_concat]
    rw [pot_true t0, hbtop]
    rw [pot_true tm] at hrest
    exact le_trans hkey hrest
  · -- speedO: a configuration block and an index block are opened at once
    have hbs : bs.length = k := by
      rw [e0] at hp; simp only [List.length_append, List.length_singleton] at hp; omega
    have hl1 : (L (p + 1)).1.length = k + 3 := by
      rw [e1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have hb0 : 0 ≤ b := by
      have := hNNp.1 bs.length; rwa [e0, getD_snoc_len] at this
    have hlen2 : p + 1 < p + len := by
      by_contra hc'; have : len = 1 := by omega
      subst this; rw [hl1] at hq; omega
    obtain ⟨m1, hm11, hm12, hm13, hm14⟩ := first_return L (p + 1) (p + len) (k + 2) hlen2
      (by omega)
    have hdm1 : k + 3 ≤ (L (m1 - 1)).1.length := by
      rcases Nat.eq_or_lt_of_le (show p + 1 ≤ m1 - 1 by omega) with h | h
      · rw [← h, hl1]
      · have := hm14 (m1 - 1) h (by omega); omega
    have hm1k : (L m1).1.length = k + 2 := by
      have h1 := tstep_len (hstep (m1 - 1) (by omega) (by omega))
      rw [show m1 - 1 + 1 = m1 by omega] at h1
      omega
    have hd1 : ∀ i, p + 1 ≤ i → i < m1 → k + 3 ≤ (L i).1.length := by
      intro i h1 h2
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · rw [← h, hl1]
      · have := hm14 i h h2; omega
    obtain ⟨tm1, hcost1⟩ := excursion hc0 L len (fun len' p' k' h' => ih len' h' p' k') (p + 1) m1
      (k + 2) hm11 (by omega) (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => ⟨hd1 i h1 h2, (hdep i (by omega) (by omega)).2⟩) hl1 hm1k
    have hpot1 : pot c (L (p + 1)) = Ps c b₂ (c * Ps c b₂ (L (p + 1)).2.2) := by
      rw [pot_false t1, e1, show bs ++ [b, b₁, b₂] = (bs ++ [b, b₁]) ++ [b₂] by simp, top_concat]
    have hW : Ps c b (c * Ps c b ((L p).2.2 - x)) ≤ pot c (L (p + 1)) := by
      rw [hpot1]
      exact ps_mono hc0 h₂ (mul_le_mul_of_nonneg_left (ps_mono hc0 h₂ h₃) hc0)
    have hent1 := entry_mono L (k + 1) (m1 - (p + 1)) (p + 1)
      (fun i h1 h2 => hstep i (by omega) (by omega)) (fun i h1 h2 => hd1 i h1 (by omega))
    rw [show p + 1 + (m1 - (p + 1)) = m1 by omega] at hent1
    have hb1 : (L (p + 1)).1.getD (k + 1) 0 = b₁ := by
      rw [e1, List.getD_append_right _ _ _ _ (by omega), hbs, show k + 1 - k = 1 by omega]; rfl
    have hTm : max x b ≤ top (L m1).1 := by
      rw [top_of_len hm1k]; rw [hb1] at hent1; exact le_trans h₁ hent1
    have hkey := key (b := b) (a := (L p).2.2) (x := x) (T := top (L m1).1) (E := (L m1).2.2)
      hc3 hc2 hb0 hx hxa (le_trans (le_max_left _ _) hTm) (le_trans (le_max_right _ _) hTm)
      (le_trans (mul_le_mul_of_nonneg_left (max_le_max le_rfl hW) hc0) hcost1)
    rw [← pot_true tm1] at hkey
    have hlen3 : m1 < p + len := by
      by_contra hc'; have : m1 = p + len := by omega
      rw [this, hq] at hm1k; omega
    obtain ⟨m0, hm01, hm02, hm03, hm04⟩ := first_return L m1 (p + len) (k + 1) hlen3 (by omega)
    have hm0k : (L m0).1.length = k + 1 := by
      have := (hdep m0 (by omega) hm02).1; omega
    have hd0 : ∀ i, m1 ≤ i → i < m0 → k + 2 ≤ (L i).1.length := by
      intro i h1 h2
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · rw [← h, hm1k]
      · have := hm04 i h h2; omega
    obtain ⟨tm0, hcost0⟩ := excursion hc0 L len (fun len' p' k' h' => ih len' h' p' k') m1 m0
      (k + 1) hm01 (by omega) (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => ⟨hd0 i h1 h2, (hdep i (by omega) (by omega)).2⟩) hm1k hm0k
    have hent0 := entry_mono L k (m0 - (p + 1)) (p + 1)
      (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => by
        rcases lt_or_ge i m1 with h | h
        · have := hd1 i h1 h; omega
        · exact hd0 i h (by omega))
    rw [show p + 1 + (m0 - (p + 1)) = m0 by omega] at hent0
    have hbk : (L (p + 1)).1.getD k 0 = b := by
      rw [e1, List.getD_append_right _ _ _ _ (by omega), hbs, Nat.sub_self]; rfl
    rw [hbk, ← top_of_len hm0k] at hent0
    have hrest := ih (p + len - m0) (by omega) m0 k (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => hdep i (by omega) (by omega)) hm0k
      (by rw [show m0 + (p + len - m0) = p + len by omega]; exact hq)
    rw [show m0 + (p + len - m0) = p + len by omega] at hrest
    have hbtop : top (L p).1 = b := by rw [e0, top_concat]
    refine le_trans ?_ hrest
    rw [pot_false t0, hbtop, pot_true tm0]
    apply ps_mono hc0 hent0
    refine le_trans ?_ hcost0
    exact mul_le_mul_of_nonneg_left (le_trans hkey (le_max_right _ _)) hc0
  · -- flip
    have hl1 : (L (p + 1)).1.length = k + 1 := by rw [e1, ← e0]; exact hp
    have hrest := ih (len - 1) (by omega) (p + 1) k (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => hdep i (by omega) (by omega)) hl1
      (by rw [show p + 1 + (len - 1) = p + len by omega]; exact hq)
    rw [show p + 1 + (len - 1) = p + len by omega] at hrest
    refine le_trans ?_ hrest
    have hb0 : 0 ≤ b := by have := hNNp.1 bs.length; rwa [e0, getD_snoc_len] at this
    have ha0 := hNNp.2
    have htp : top (L p).1 = b := by rw [e0, top_concat]
    have htp1 : top (L (p + 1)).1 = b := by rw [e1, top_concat]
    cases ht : (L p).2.1 with
    | true =>
      have t1' : (L (p + 1)).2.1 = false := by rw [t1, ht]; rfl
      rw [pot_true ht, pot_false t1', htp, htp1]
      apply ps_mono hc0 le_rfl
      have e2 : c / 2 * (L (p + 1)).2.2 ≤ Ps c b (L (p + 1)).2.2 :=
        ps_ge_g hc0 hc2 (le_trans (mul_nonneg hc0 (le_trans ha0 (le_max_right _ _))) hf)
      have e3 : c * (L p).2.2 ≤ (L (p + 1)).2.2 := le_trans (mul_le_mul_of_nonneg_left
        (le_max_right _ _) hc0) hf
      have e4 : c * (c / 2 * (c * (L p).2.2)) ≤ c * Ps c b (L (p + 1)).2.2 :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left e3 (by linarith)) e2) hc0
      have e5 : c * (c / 2 * (c * (L p).2.2)) = c ^ 3 / 2 * (L p).2.2 := by ring
      have e6 : (L p).2.2 ≤ c ^ 3 / 2 * (L p).2.2 := by nlinarith
      linarith
    | false =>
      have t1' : (L (p + 1)).2.1 = true := by rw [t1, ht]; rfl
      rw [pot_false ht, pot_true t1', htp, htp1]
      apply ps_mono hc0 le_rfl
      exact le_trans (mul_le_mul_of_nonneg_left ps_le_max hc0) hf
  · -- pop: impossible inside a segment
    have := (hdep (p + 1) (by omega) (by omega)).1
    rw [e1] at this; rw [e0] at hp
    simp only [List.length_append, List.length_singleton] at hp
    omega
  · -- weak
    have hl1 : (L (p + 1)).1.length = k + 1 := by rw [hl, hp]
    have hrest := ih (len - 1) (by omega) (p + 1) k (fun i h1 h2 => hstep i (by omega) (by omega))
      (fun i h1 h2 => hdep i (by omega) (by omega)) hl1
      (by rw [show p + 1 + (len - 1) = p + len by omega]; exact hq)
    rw [show p + 1 + (len - 1) = p + len by omega] at hrest
    refine le_trans ?_ hrest
    have htop : top (L p).1 ≤ top (L (p + 1)).1 := by
      rw [top_of_len hp, top_of_len hl1]; exact hle k
    unfold pot
    rw [t1]
    split_ifs
    · exact ps_mono hc0 htop ha
    · exact ps_mono hc0 htop (mul_le_mul_of_nonneg_left (ps_mono hc0 htop ha) hc0)

/-- **Limit of the reduced calculus.** For every c with c³ ≥ 4 there is no normal-form
refutation in `TStep c`, strict (a' < a) or non-strict (a' = a). (The proof shows that the
final exponent is at least (min(c,2)²/2)·a; that bound is not stated as a separate theorem.) -/
theorem no_trefutation {c : ℝ} (hc3 : 4 ≤ c ^ 3) (n : ℕ) (L : ℕ → TLine) : ¬ TRefutes c n L := by
  rintro ⟨hn, h0, hN, ha0, hle, hstep, hmid⟩
  have hc0 : 0 ≤ c := by
    by_contra h; push Not at h
    have : c ^ 3 < 0 := by
      have : c ^ 3 = c * c ^ 2 := by ring
      have hsq : 0 < c ^ 2 := by nlinarith
      rw [this]; exact mul_neg_of_neg_of_pos h hsq
    linarith
  set c₀ := min c 2 with hc₀
  have hc₀2 : c₀ ≤ 2 := min_le_right _ _
  have hc₀3 : 4 ≤ c₀ ^ 3 := by
    rcases le_total c 2 with h | h
    · rw [hc₀, min_eq_left h]; exact hc3
    · rw [hc₀, min_eq_right h]; norm_num
  obtain ⟨hc15, hcsq, -, -, -⟩ := cfacts hc₀3 hc₀2
  have hc₀0 : 0 ≤ c₀ := by linarith
  have hNN : ∀ i, i ≤ n → NN (L i) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨fun i => by rw [h0]; simp, ha0.le⟩
    | succ i ih => intro hi; exact tstep_nonneg hc0 (hstep i (by omega)) (ih (by omega))
  have hs : ∀ i < n, TStep c₀ (L i) (L (i + 1)) := fun i hi =>
    tstep_restrict (min_le_left _ _) (hstep i hi) (hNN i hi.le)
  have hL1 : (L 1).1 = [0] ∧ (L 1).2.1 = true ∧ (L 1).2.2 = (L 0).2.2 := by
    rcases tstep_inv (hs 0 (by omega)) with ⟨-, e1, t1, e2⟩ |
      ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -⟩ | ⟨bs, b, x, b₁, b₂, -, -, -, -, -, e0, -⟩ |
      ⟨bs, b, e0, -⟩ | ⟨bs, b, e0, -⟩ | ⟨hl, -⟩
    · exact ⟨e1, t1, e2⟩
    all_goals first
      | (rw [h0] at e0; simp at e0)
      | (exact absurd (List.length_eq_zero_iff.mp (by rw [hl, h0]; rfl)) (hmid 1 (by omega) (by omega)))
  obtain ⟨e1, t1, e2⟩ := hL1
  have hseg : ∀ len p k, len < n + 1 → SegStmt c₀ L len p k :=
    fun len p k _ => segment hc₀3 hc₀2 L len p k
  have hex := excursion hc₀0 L (n + 1) hseg 1 n 0 (by omega) (by omega)
    (fun i h1 h2 => hs i h2)
    (fun i h1 h2 => ⟨Nat.one_le_iff_ne_zero.mpr (fun h => hmid i (by omega) h2
      (List.length_eq_zero_iff.mp h)), hNN i h2.le⟩)
    (by rw [e1]; rfl) (by rw [hN]; rfl)
  obtain ⟨-, hcost⟩ := hex
  have hpot : pot c₀ (L 1) = Ps c₀ 0 (L 0).2.2 := by
    rw [pot_true t1, e1, e2]; rfl
  have hg : c₀ / 2 * (L 0).2.2 ≤ pot c₀ (L 1) := by
    rw [hpot]; exact ps_ge_g hc₀0 hc₀2 ha0.le
  have h1 : c₀ * (c₀ / 2 * (L 0).2.2) ≤ (L n).2.2 :=
    le_trans (mul_le_mul_of_nonneg_left (le_trans hg (le_max_right _ _)) hc₀0) hcost
  have h2 : c₀ * (c₀ / 2 * (L 0).2.2) = c₀ ^ 2 / 2 * (L 0).2.2 := by ring
  have h3 : 5 / 4 * (L 0).2.2 ≤ c₀ ^ 2 / 2 * (L 0).2.2 :=
    mul_le_mul_of_nonneg_right (by linarith) ha0.le
  linarith

/-- Non-vacuity: W13's 5-line example (annotation 1000) refutes at c = 13/10. -/
noncomputable def tlv : ℕ → TLine
  | 0 => ([], true, 1)
  | 1 => ([0], true, 1)
  | 2 => ([14 / 25, 0], false, 11 / 25)
  | 3 => ([14 / 25, 0], true, 143 / 250)
  | 4 => ([14 / 25], true, 1859 / 2500)
  | _ => ([], true, 24167 / 25000)

theorem tlv_refutes : TRefutes (13 / 10) 5 tlv := by
  refine ⟨by norm_num, rfl, rfl, by norm_num [tlv], by norm_num [tlv], ?_, ?_⟩
  · intro i hi
    rcases i with _ | _ | _ | _ | _ | i
    · exact TStep.init 1
    · exact TStep.speedM [] 0 1 (14 / 25) (14 / 25) 0 (11 / 25) (by norm_num) (by norm_num)
        (by norm_num) le_rfl (by norm_num)
    · exact TStep.flip (c := 13 / 10) [14 / 25] 0 (11 / 25) (143 / 250) false (by norm_num)
    · exact TStep.pop (c := 13 / 10) [14 / 25] 0 (143 / 250) (1859 / 2500) (by norm_num [top])
    · exact TStep.pop (c := 13 / 10) [] (14 / 25) (1859 / 2500) (24167 / 25000) (by norm_num [top])
    · omega
  · intro i h1 h2
    rcases i with _ | _ | _ | _ | _ | i
    · omega
    all_goals first | omega | simp [tlv]

theorem refutes_below_cbrt4 : ∃ c : ℝ, c ^ 3 < 4 ∧ ∃ n L, TRefutes c n L :=
  ⟨13 / 10, by norm_num, 5, tlv, tlv_refutes⟩

end TL
end PastaMath.TautThreshold
