-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Potential

/-!
# A finite check of the Lemma 7.1 condition for all words

`absCheck` is an executable checker over ℚ that discharges `HLM.Hyp` (the Lemma 7.1 condition
`ConvOK` for every nonempty word, of any length) from a finite list of abstract word states.

A word's state is (A, L, D, m) = (Ad w, AL w, D w, |w|). Prepending a letter p maps it to
(max(κ_p, θ_p·A), θ_p·A, 1/κ_p + D/θ_p, m + 1) (`prepQ`). This map is monotone for the order
"A, L, m larger and D smaller" (`Dom`, `dom_prep`), and `ConvOK` transfers along that order
(`convOK_mono`; the m-monotonicity of Qf uses A·D ≥ 1, which holds for real words by
`AdDw_ge_one`). A state is *done* once θ₀/c ≤ A·L·d/(A + L·d): then `ConvOK` holds there
(`convOK_done`) and the condition persists under prepending.

`absCheck c d θ₀ lv S` accepts when 1 ≤ c, 0 ≤ d, every level has 1 ≤ θ ≤ c and P ≥ 0, every
state of S has A > 0, L ≥ 0, D > 0 and an interval certificate for `ConvOK` (`ivOK`: a list of
breakpoints in the ratio a/b, starting at 0, with one level per piece whose term is below
max(A·b, Qf·a) on that piece), and S together with the state (1, 0, 1, 0) of the empty word is
closed under prepending each letter, up to done states and domination by a state of S.
`absCheck_sound` turns acceptance into `Hyp` for the levels cast to ℝ.
-/

namespace PastaMath.OneTapeThreshold
namespace HLM

/-- A rational word state (A, L, D, m). -/
structure St where
  A : ℚ
  L : ℚ
  D : ℚ
  m : ℕ

def kapQ (c : ℚ) (p : ℚ × ℚ) : ℚ := max c p.1

/-- The state after prepending the letter p: (max(κ_p, θ_p·A), θ_p·A, 1/κ_p + D/θ_p, m + 1). -/
def prepQ (c : ℚ) (p : ℚ × ℚ) (s : St) : St :=
  ⟨max (kapQ c p) (p.2 * s.A), p.2 * s.A, 1 / kapQ c p + s.D / p.2, s.m + 1⟩

/-- Qf of a state, over ℚ. -/
def QfQ (d : ℚ) (s : St) : ℚ :=
  max (s.A * s.L * d / (s.A + s.L * d)) (s.A * (1 + s.m * d) / (s.A * s.D + s.m * d))

/-- θ₀/c ≤ A·L·d/(A + L·d). -/
def doneQ (c d θ₀ : ℚ) (s : St) : Bool := decide (θ₀ / c ≤ s.A * s.L * d / (s.A + s.L * d))

/-- `domQ s t`: s has A, L, m at least and D at most those of t. -/
def domQ (s t : St) : Bool := decide (t.A ≤ s.A) && decide (t.L ≤ s.L) && decide (s.D ≤ t.D) && decide (t.m ≤ s.m)

/-- Interval certificate for `ConvOK` at slope q and coefficient A: a list of pieces (y_k, j_k) with
nondecreasing y_k; on the piece a/b ≥ y_k (up to y_{k+1}), level j_k satisfies P ≤ A or P ≤ q·y_k, and
θ/c·y_{k+1} ≤ A or θ/c ≤ q (θ/c ≤ q on the last piece). -/
def ivOK (c q A : ℚ) (lt : List (ℚ × ℚ)) : List (ℚ × ℕ) → Bool
  | [] => false
  | [(y, j)] =>
      match lt[j]? with
      | none => false
      | some p => (decide (p.1 ≤ A) || decide (p.1 ≤ q * y)) && decide (p.2 / c ≤ q)
  | (y, j) :: (y', j') :: rest =>
      match lt[j]? with
      | none => false
      | some p => (decide (p.1 ≤ A) || decide (p.1 ≤ q * y)) &&
          (decide (p.2 / c * y' ≤ A) || decide (p.2 / c ≤ q)) && decide (y ≤ y') &&
          ivOK c q A lt ((y', j') :: rest)

/-- A > 0, L ≥ 0, D > 0, and an interval certificate starting at 0 for slope Qf. -/
def stOK (c d : ℚ) (lt : List (ℚ × ℚ)) (s : St) (iv : List (ℚ × ℕ)) : Bool :=
  decide (0 < s.A) && decide (0 ≤ s.L) && decide (0 < s.D) &&
  (match iv with | (y, _) :: _ => decide (y = 0) | [] => false) && ivOK c (QfQ d s) s.A lt iv

/-- Prepending any letter to s gives a done state or a state that dominates some state of S. -/
def closedQ (c d θ₀ : ℚ) (lt : List (ℚ × ℚ)) (S : List (St × List (ℚ × ℕ))) (s : St) : Bool :=
  lt.all fun p => doneQ c d θ₀ (prepQ c p s) || S.any fun t => domQ (prepQ c p s) t.1

/-- Accepts when 1 ≤ c, 0 ≤ d, every level of (0, θ₀) :: lv has 1 ≤ θ ≤ c and P ≥ 0, every
state of S passes `stOK`, and the empty word's state (1, 0, 1, 0) and every state of S pass `closedQ`. -/
def absCheck (c d θ₀ : ℚ) (lv : List (ℚ × ℚ)) (S : List (St × List (ℚ × ℕ))) : Bool :=
  decide (1 ≤ c) && decide (0 ≤ d) &&
  ((0, θ₀) :: lv).all (fun p => decide (1 ≤ p.2) && decide (p.2 ≤ c) && decide (0 ≤ p.1)) &&
  S.all (fun t => stOK c d ((0, θ₀) :: lv) t.1 t.2) &&
  closedQ c d θ₀ ((0, θ₀) :: lv) S ⟨1, 0, 1, 0⟩ &&
  S.all (fun t => closedQ c d θ₀ ((0, θ₀) :: lv) S t.1)

noncomputable section

def castP (p : ℚ × ℚ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

/-- `Dom A L D m A' L' D' m'`: A' ≤ A, L' ≤ L, D ≤ D' and m' ≤ m. -/
def Dom (A L D : ℝ) (m : ℕ) (A' L' D' : ℝ) (m' : ℕ) : Prop := A' ≤ A ∧ L' ≤ L ∧ D ≤ D' ∧ m' ≤ m

variable {c d θ₀ : ℝ} {lv : List (ℝ × ℝ)}

theorem Q1_mono {d A L A' L' : ℝ} (hd : 0 ≤ d) (hA : 0 < A) (hL : 0 ≤ L) (hAA : A ≤ A') (hLL : L ≤ L') :
    A * L * d / (A + L * d) ≤ A' * L' * d / (A' + L' * d) := by
  have hA' : 0 < A' := lt_of_lt_of_le hA hAA
  have h1 : 0 < A + L * d := by have := mul_nonneg hL hd; linarith
  have h2 : 0 < A' + L' * d := by have := mul_nonneg (le_trans hL hLL) hd; linarith
  rw [div_le_div_iff₀ h1 h2]
  have e : A' * L' * d * (A + L * d) - A * L * d * (A' + L' * d) =
      A * A' * d * (L' - L) + L * L' * d * d * (A' - A) := by ring
  have : 0 ≤ A * A' * d * (L' - L) + L * L' * d * d * (A' - A) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hA.le hA'.le) hd) (sub_nonneg.2 hLL)
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hL (le_trans hL hLL)) hd) hd) (sub_nonneg.2 hAA)
    linarith
  linarith

theorem Q2_mono {d A D A' D' : ℝ} {m m' : ℕ} (hd : 0 ≤ d) (hA : 0 < A) (hD : 0 < D) (hAA : A ≤ A')
    (hDD : D' ≤ D) (hD' : 0 < D') (hmm : m ≤ m') (hAD : 1 ≤ A' * D') :
    A * (1 + m * d) / (A * D + m * d) ≤ A' * (1 + m' * d) / (A' * D' + m' * d) := by
  have hA' : 0 < A' := lt_of_lt_of_le hA hAA
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm' : (m : ℝ) ≤ m' := Nat.cast_le.2 hmm
  have hmd : 0 ≤ (m : ℝ) * d := mul_nonneg hm hd
  have hm'd : 0 ≤ (m' : ℝ) * d := mul_nonneg (le_trans hm hm') hd
  have p1 : 0 < A * D + m * d := by have := mul_pos hA hD; linarith
  have p2 : 0 < A' * D + m * d := by have := mul_pos hA' hD; linarith
  have p3 : 0 < A' * D' + m * d := by have := mul_pos hA' hD'; linarith
  have p4 : 0 < A' * D' + m' * d := by have := mul_pos hA' hD'; linarith
  have s1 : A * (1 + m * d) / (A * D + m * d) ≤ A' * (1 + m * d) / (A' * D + m * d) := by
    rw [div_le_div_iff₀ p1 p2]
    have : A' * (1 + m * d) * (A * D + m * d) - A * (1 + m * d) * (A' * D + m * d) =
        (1 + m * d) * (m * d) * (A' - A) := by ring
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + m * d) hmd) (sub_nonneg.2 hAA)]
  have s2 : A' * (1 + m * d) / (A' * D + m * d) ≤ A' * (1 + m * d) / (A' * D' + m * d) := by
    apply div_le_div_of_nonneg_left (by positivity) p3
    nlinarith [mul_le_mul_of_nonneg_left hDD hA'.le]
  have s3 : A' * (1 + m * d) / (A' * D' + m * d) ≤ A' * (1 + m' * d) / (A' * D' + m' * d) := by
    rw [div_le_div_iff₀ p3 p4]
    have : A' * (1 + m' * d) * (A' * D' + m * d) - A' * (1 + m * d) * (A' * D' + m' * d) =
        A' * ((m' : ℝ) - m) * d * (A' * D' - 1) := by ring
    have : 0 ≤ A' * ((m' : ℝ) - m) * d * (A' * D' - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg hA'.le (sub_nonneg.2 hm')) hd) (sub_nonneg.2 hAD)
    linarith
  exact le_trans s1 (le_trans s2 s3)

theorem Qf_mono {d A L D A' L' D' : ℝ} {m m' : ℕ} (hd : 0 ≤ d) (hA : 0 < A) (hL : 0 ≤ L) (hD : 0 < D)
    (hdom : Dom A' L' D' m' A L D m) (hD' : 0 < D') (hAD : 1 ≤ A' * D') : Qf d A L D m ≤ Qf d A' L' D' m' := by
  obtain ⟨hAA, hLL, hDD, hmm⟩ := hdom
  unfold Qf
  exact max_le_max (Q1_mono hd hA hL hAA hLL) (Q2_mono hd hA hD hAA hDD hD' hmm hAD)

/-- For d ≥ 0, A > 0, L ≥ 0, D > 0, D' > 0 and A'·D' ≥ 1: if (A', L', D', m') dominates
(A, L, D, m), `ConvOK` at the latter implies `ConvOK` at the former. -/
theorem convOK_mono (H0 : 0 ≤ d) {A L D A' L' D' : ℝ} {m m' : ℕ} (hA : 0 < A) (hL : 0 ≤ L) (hD : 0 < D)
    (hdom : Dom A' L' D' m' A L D m) (hD' : 0 < D') (hAD : 1 ≤ A' * D')
    (h : ConvOK c d θ₀ lv A L D m) : ConvOK c d θ₀ lv A' L' D' m' := by
  intro b a hb ha
  refine le_trans (h b a hb ha) (max_le_max (mul_le_mul_of_nonneg_right hdom.1 hb) ?_)
  exact mul_le_mul_of_nonneg_right (Qf_mono H0 hA hL hD hdom hD' hAD) ha

/-- For c > 0, d ≥ 0, A > 0 and L ≥ 0: if θ₀/c ≤ A·L·d/(A + L·d) then `ConvOK` holds at
(A, L, D, m), for every D and m. -/
theorem convOK_done (_hc : 0 < c) (_hd : 0 ≤ d) {A L D : ℝ} {m : ℕ} (_hA : 0 < A) (_hL : 0 ≤ L)
    (h : θ₀ / c ≤ A * L * d / (A + L * d)) : ConvOK c d θ₀ lv A L D m := by
  intro b a hb ha
  refine le_trans (Tm_le_base b a) (le_trans ?_ (le_max_right _ _))
  exact mul_le_mul_of_nonneg_right (le_trans h (le_max_left _ _)) ha

/-- Let c > 0 be the cast of the rational cq, q ≥ 0, and let every level of the rational list lt
cast into (0, θ₀) :: lv and have θ ≥ 0. If `ivOK cq q A lt ((y, j) :: rest)` accepts, then
Tm(b, a) ≤ max(A·b, q·a) for all b, a ≥ 0 with y·b ≤ a. -/
theorem ivOK_sound (hc : 0 < c) {cq q A : ℚ} {lt : List (ℚ × ℚ)} (hcq : (cq : ℝ) = c) (hq : 0 ≤ (q : ℝ))
    (hlt : ∀ p ∈ lt, castP p ∈ (0, θ₀) :: lv) (hlt0 : ∀ p ∈ lt, (0 : ℝ) ≤ p.2) :
    ∀ (rest : List (ℚ × ℕ)) (y : ℚ) (j : ℕ), ivOK cq q A lt ((y, j) :: rest) = true →
      ∀ b a : ℝ, 0 ≤ b → 0 ≤ a → (y : ℝ) * b ≤ a → Tm c θ₀ lv b a ≤ max ((A : ℝ) * b) ((q : ℝ) * a) := by
  intro rest
  induction rest with
  | nil =>
    intro y j hok b a hb ha hya
    simp only [ivOK] at hok
    cases hp : lt[j]? with
    | none => rw [hp] at hok; simp at hok
    | some p =>
      rw [hp] at hok
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hP, hθ⟩ := hok
      have hmem := hlt p (List.mem_of_getElem? hp)
      refine le_trans (Tm_le_letter hmem ha) (max_le ?_ ?_)
      · show (p.1 : ℝ) * b ≤ _
        rcases hP with hP | hP
        · exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hP) hb) (le_max_left _ _)
        · refine le_trans ?_ (le_max_right _ _)
          have : (p.1 : ℝ) ≤ q * y := by exact_mod_cast hP
          calc (p.1 : ℝ) * b ≤ (q * y) * b := mul_le_mul_of_nonneg_right this hb
            _ = q * (y * b) := by ring
            _ ≤ q * a := mul_le_mul_of_nonneg_left hya hq
      · show (p.2 : ℝ) / c * a ≤ _
        refine le_trans ?_ (le_max_right _ _)
        have : (p.2 : ℝ) / c ≤ q := by rw [← hcq]; exact_mod_cast hθ
        exact mul_le_mul_of_nonneg_right this ha
  | cons nx rest ih =>
    intro y j hok b a hb ha hya
    obtain ⟨y', j'⟩ := nx
    simp only [ivOK] at hok
    cases hp : lt[j]? with
    | none => rw [hp] at hok; simp at hok
    | some p =>
      rw [hp] at hok
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨hP, hθ⟩, hyy⟩, hrest⟩ := hok
      rcases le_or_gt ((y' : ℝ) * b) a with h' | h'
      · exact ih y' j' hrest b a hb ha h'
      · have hmem := hlt p (List.mem_of_getElem? hp)
        refine le_trans (Tm_le_letter hmem ha) (max_le ?_ ?_)
        · show (p.1 : ℝ) * b ≤ _
          rcases hP with hP | hP
          · exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hP) hb) (le_max_left _ _)
          · refine le_trans ?_ (le_max_right _ _)
            have : (p.1 : ℝ) ≤ q * y := by exact_mod_cast hP
            calc (p.1 : ℝ) * b ≤ (q * y) * b := mul_le_mul_of_nonneg_right this hb
              _ = q * (y * b) := by ring
              _ ≤ q * a := mul_le_mul_of_nonneg_left hya hq
        · show (p.2 : ℝ) / c * a ≤ _
          have hθ0 : 0 ≤ (p.2 : ℝ) / c := div_nonneg (hlt0 p (List.mem_of_getElem? hp)) hc.le
          rcases hθ with hθ | hθ
          · refine le_trans ?_ (le_max_left _ _)
            have hθ' : (p.2 : ℝ) / c * y' ≤ A := by rw [← hcq]; exact_mod_cast hθ
            calc (p.2 : ℝ) / c * a ≤ (p.2 : ℝ) / c * (y' * b) := mul_le_mul_of_nonneg_left h'.le hθ0
              _ = ((p.2 : ℝ) / c * y') * b := by ring
              _ ≤ A * b := mul_le_mul_of_nonneg_right hθ' hb
          · refine le_trans ?_ (le_max_right _ _)
            have : (p.2 : ℝ) / c ≤ q := by rw [← hcq]; exact_mod_cast hθ
            exact mul_le_mul_of_nonneg_right this ha

/-- A word state is done: Lemma 7.1 holds for it and for every extension. -/
def Done (c d θ₀ A L : ℝ) : Prop := θ₀ / c ≤ A * L * d / (A + L * d)

theorem castP_mem {θq : ℚ} {lvq : List (ℚ × ℚ)} {p : ℝ × ℝ}
    (hp : p ∈ ((0 : ℝ), (θq : ℝ)) :: lvq.map castP) : ∃ q ∈ ((0 : ℚ), θq) :: lvq, p = castP q := by
  simp only [List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · exact ⟨(0, θq), by simp, by simp [castP]⟩
  · exact ⟨q, by simp [hq], rfl⟩

theorem castP_mem' {θq : ℚ} {lvq : List (ℚ × ℚ)} {q : ℚ × ℚ} (hq : q ∈ ((0 : ℚ), θq) :: lvq) :
    castP q ∈ ((0 : ℝ), (θq : ℝ)) :: lvq.map castP := by
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · simp [castP]
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hq)

theorem prepQ_cast (cq : ℚ) (q : ℚ × ℚ) (s : St) :
    ((prepQ cq q s).A : ℝ) = max (kap (cq : ℝ) (castP q)) ((q.2 : ℝ) * s.A) ∧
    ((prepQ cq q s).L : ℝ) = (q.2 : ℝ) * s.A ∧
    ((prepQ cq q s).D : ℝ) = 1 / kap (cq : ℝ) (castP q) + (s.D : ℝ) / q.2 ∧
    (prepQ cq q s).m = s.m + 1 := by
  refine ⟨by simp [prepQ, kapQ, kap, castP], by simp [prepQ], by simp [prepQ, kapQ, kap, castP], rfl⟩

theorem QfQ_cast (dq : ℚ) (s : St) : ((QfQ dq s : ℚ) : ℝ) = Qf (dq : ℝ) s.A s.L s.D s.m := by
  simp only [QfQ, Qf]; push_cast; rfl

theorem doneQ_cast {cq dq θq : ℚ} {s : St} (h : doneQ cq dq θq s = true) :
    Done (cq : ℝ) (dq : ℝ) (θq : ℝ) s.A s.L := by
  simp only [doneQ, decide_eq_true_eq] at h
  unfold Done
  exact_mod_cast h

theorem domQ_cast {s t : St} (h : domQ s t = true) : Dom s.A s.L s.D s.m t.A t.L t.D t.m := by
  simp only [domQ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, h4⟩

theorem dom_trans {A L D A' L' D' A'' L'' D'' : ℝ} {m m' m'' : ℕ} (h1 : Dom A L D m A' L' D' m')
    (h2 : Dom A' L' D' m' A'' L'' D'' m'') : Dom A L D m A'' L'' D'' m'' :=
  ⟨le_trans h2.1 h1.1, le_trans h2.2.1 h1.2.1, le_trans h1.2.2.1 h2.2.2.1, le_trans h2.2.2.2 h1.2.2.2⟩

theorem dom_prep {κ θ A L D A' L' D' : ℝ} {m m' : ℕ} (hθ : 0 < θ) (h : Dom A L D m A' L' D' m') :
    Dom (max κ (θ * A)) (θ * A) (1 / κ + D / θ) (m + 1) (max κ (θ * A')) (θ * A') (1 / κ + D' / θ) (m' + 1) :=
  ⟨max_le_max le_rfl (mul_le_mul_of_nonneg_left h.1 hθ.le), mul_le_mul_of_nonneg_left h.1 hθ.le,
    by have := div_le_div_of_nonneg_right h.2.2.1 hθ.le; linarith, by have := h.2.2.2; omega⟩

theorem done_mono {c d θ₀ A L A' L' : ℝ} (hd : 0 ≤ d) (hA : 0 < A) (hL : 0 ≤ L) (hAA : A ≤ A') (hLL : L ≤ L')
    (h : Done c d θ₀ A L) : Done c d θ₀ A' L' :=
  le_trans h (Q1_mono hd hA hL hAA hLL)

/-- If `absCheck c d θ₀ lv S = true` then `Hyp c d θ₀ lv` holds for the data cast to ℝ. -/
theorem absCheck_sound {cq dq θq : ℚ} {lvq : List (ℚ × ℚ)} {S : List (St × List (ℚ × ℕ))}
    (h : absCheck cq dq θq lvq S = true) : Hyp (cq : ℝ) (dq : ℝ) (θq : ℝ) (lvq.map castP) := by
  simp only [absCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hc1, hd0⟩, hlet⟩, hS⟩, hinit⟩, hclos⟩ := h
  set c : ℝ := (cq : ℝ)
  set d : ℝ := (dq : ℝ)
  set θ₀ : ℝ := (θq : ℝ)
  set lv := lvq.map castP
  have hc1' : (1 : ℝ) ≤ c := by show (1 : ℝ) ≤ (cq : ℝ); exact_mod_cast hc1
  have hc0 : (0 : ℝ) < c := by linarith
  have hd0' : (0 : ℝ) ≤ d := by show (0 : ℝ) ≤ (dq : ℝ); exact_mod_cast hd0
  have hletR : ∀ p ∈ (0, θ₀) :: lv, 1 ≤ p.2 ∧ p.2 ≤ c ∧ 0 ≤ p.1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := castP_mem hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hlet q hq
    exact ⟨show (1 : ℝ) ≤ (q.2 : ℝ) by exact_mod_cast h1, show (q.2 : ℝ) ≤ (cq : ℝ) by exact_mod_cast h2,
      show (0 : ℝ) ≤ (q.1 : ℝ) by exact_mod_cast h3⟩
  have HB : Base c d θ₀ lv := ⟨hc1', hd0', fun p hp => (hletR p hp).1, fun p hp => (hletR p hp).2.1,
    fun p hp => (hletR p hp).2.2⟩
  set lt : List (ℚ × ℚ) := ((0 : ℚ), θq) :: lvq
  have hlt : ∀ q ∈ lt, castP q ∈ (0, θ₀) :: lv := fun q hq => castP_mem' hq
  have hq1 : ∀ q ∈ lt, (1 : ℝ) ≤ q.2 := fun q hq => (hletR _ (hlt q hq)).1
  have hlt0 : ∀ q ∈ lt, (0 : ℝ) ≤ q.2 := fun q hq => by linarith [hq1 q hq]
  have hθq : ∀ q ∈ lt, (0 : ℝ) < q.2 := fun q hq => by linarith [hq1 q hq]
  have hSok : ∀ t ∈ S, stOK cq dq lt t.1 t.2 = true := fun t ht => hS t ht
  have hSpos : ∀ t ∈ S, (0 : ℝ) < t.1.A ∧ (0 : ℝ) ≤ t.1.L ∧ (0 : ℝ) < t.1.D := by
    intro t ht
    have := hSok t ht
    simp only [stOK, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩ := this
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
  have step : ∀ (s : St), closedQ cq dq θq lt S s = true → (0 : ℝ) ≤ s.A →
      ∀ (w : List (ℝ × ℝ)), Wd θ₀ lv w → ∀ q ∈ lt,
      Dom (Ad c w) (AL c w) (Dw c w) w.length s.A s.L s.D s.m →
      Done c d θ₀ (Ad c (castP q :: w)) (AL c (castP q :: w)) ∨
        ∃ t ∈ S, Dom (Ad c (castP q :: w)) (AL c (castP q :: w)) (Dw c (castP q :: w))
          (castP q :: w).length t.1.A t.1.L t.1.D t.1.m := by
    intro s hcl hsA w hw q hq hdom
    have hc := hcl
    simp only [closedQ, List.all_eq_true, Bool.or_eq_true, List.any_eq_true] at hc
    obtain ⟨hA', hL', hD', hm'⟩ := prepQ_cast cq q s
    have hdp := dom_prep (κ := kap c (castP q)) (hθq q hq) hdom
    have eA : Ad c (castP q :: w) = max (kap c (castP q)) ((q.2 : ℝ) * Ad c w) := by simp [Ad, castP]
    have eL : AL c (castP q :: w) = (q.2 : ℝ) * Ad c w := by simp [AL, castP]
    have eD : Dw c (castP q :: w) = 1 / kap c (castP q) + Dw c w / q.2 := by simp [Dw, castP]
    have em : (castP q :: w).length = w.length + 1 := rfl
    have hD2 : Dom (Ad c (castP q :: w)) (AL c (castP q :: w)) (Dw c (castP q :: w)) (castP q :: w).length
        (prepQ cq q s).A (prepQ cq q s).L (prepQ cq q s).D (prepQ cq q s).m := by
      rw [eA, eL, eD, em, hA', hL', hD', hm']; exact hdp
    rcases hc q hq with hdn | ⟨t, ht, hdt⟩
    · left
      have hdone := doneQ_cast hdn
      refine done_mono hd0' ?_ ?_ hD2.1 hD2.2.1 hdone
      · rw [hA']; exact lt_of_lt_of_le hc0 (le_trans (kap_ge c _) (le_max_left _ _))
      · rw [hL']; exact mul_nonneg (hlt0 q hq) hsA
    · exact Or.inr ⟨t, ht, dom_trans hD2 (domQ_cast hdt)⟩
  have reach : ∀ w, Wd θ₀ lv w → w = [] ∨ Done c d θ₀ (Ad c w) (AL c w) ∨
      ∃ t ∈ S, Dom (Ad c w) (AL c w) (Dw c w) w.length t.1.A t.1.L t.1.D t.1.m := by
    intro w
    induction w with
    | nil => intro _; exact Or.inl rfl
    | cons p w ih =>
      intro hw
      obtain ⟨hp, hw'⟩ := wd_cons hw
      obtain ⟨q, hq, rfl⟩ := castP_mem hp
      right
      rcases ih hw' with rfl | hdn | ⟨t, ht, hdt⟩
      · have h0 : Dom (Ad c []) (AL c []) (Dw c []) ([] : List (ℝ × ℝ)).length
            ((⟨1, 0, 1, 0⟩ : St).A : ℝ) ((⟨1, 0, 1, 0⟩ : St).L : ℝ) ((⟨1, 0, 1, 0⟩ : St).D : ℝ)
            (⟨1, 0, 1, 0⟩ : St).m := by simp [Dom, Ad, AL, Dw]
        exact step _ hinit (by simp) [] hw' q hq h0
      · left
        have hA0 := Ad_pos HB hw'
        have hL0 := AL_nonneg HB w hw'
        refine done_mono hd0' hA0 hL0 ?_ ?_ hdn
        · simp only [Ad, castP]
          refine le_trans ?_ (le_max_right _ _)
          have h1 := hq1 q hq
          nlinarith
        · have h1 := hq1 q hq
          have h2 := AL_le_Ad HB w hw'
          show AL c w ≤ (q.2 : ℝ) * Ad c w
          nlinarith
      · exact step t.1 (hclos t ht) (hSpos t ht).1.le w hw' q hq hdt
  refine ⟨HB, fun w hw hne => ?_⟩
  rcases reach w hw with h0 | hdn | ⟨t, ht, hdt⟩
  · exact absurd h0 hne
  · exact convOK_done hc0 hd0' (Ad_pos HB hw) (AL_nonneg HB w hw) hdn
  · obtain ⟨htA, htL, htD⟩ := hSpos t ht
    have hok := hSok t ht
    simp only [stOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, hhead⟩, hiv⟩ := hok
    obtain ⟨⟨y, j⟩, rest, hiv_eq⟩ : ∃ yj rest, t.2 = yj :: rest := by
      cases h2 : t.2 with
      | nil => rw [h2] at hhead; simp at hhead
      | cons yj rest => exact ⟨yj, rest, rfl⟩
    rw [hiv_eq] at hhead hiv
    simp only [decide_eq_true_eq] at hhead
    have hq0 : (0 : ℝ) ≤ (QfQ dq t.1 : ℚ) := by
      rw [QfQ_cast]; unfold Qf
      refine le_trans ?_ (le_max_left _ _)
      have : 0 < (t.1.A : ℝ) + t.1.L * d := by have := mul_nonneg htL hd0'; linarith
      exact div_nonneg (mul_nonneg (mul_nonneg htA.le htL) hd0') this.le
    have hconv : ConvOK c d θ₀ lv t.1.A t.1.L t.1.D t.1.m := by
      intro b a hb ha
      have := ivOK_sound (θ₀ := θ₀) (lv := lv) hc0 rfl hq0 hlt hlt0 rest y j hiv b a hb ha
        (by rw [hhead]; simp; exact ha)
      rw [QfQ_cast] at this
      exact this
    exact convOK_mono hd0' htA htL htD hdt (Dw_pos HB w hw) (AdDw_ge_one HB w hw) hconv

end

end HLM
end PastaMath.OneTapeThreshold
