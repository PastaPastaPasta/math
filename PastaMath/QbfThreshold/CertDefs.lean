-- SPDX-License-Identifier: Apache-2.0
import PastaMath.QbfThreshold.Threshold

/-!
A ℚ transcription of W13's literal QBF_k rules (Def. 4.1 with the §5
slowdown removing up to K blocks): input superscript 1, guess exponents tracked, x ≤ a − 1, and a
normal-form checker (`checkL`) for `decide +kernel`.  `checkL_sound` maps a checked literal proof to a
`QStep` path, so the certificates are refutations in the calculus of `SibQbf.lean`.
-/

noncomputable section

namespace PastaMath.QbfThreshold

/-- Literal stack, innermost first: (guess exponent, after-superscript). -/
abbrev LStack := List (ℚ × ℚ)

def lmaxQ : List ℚ → ℚ
  | [] => 0
  | b :: l => max b (lmaxQ l)

/-- Superscript in front of the next block (1 = input length when there is none). -/
def frontQ : LStack → ℚ
  | [] => 1
  | (_, s) :: _ => s

inductive Op
  | S (x : ℚ)
  | P (j : ℕ)

def stepL (c : ℚ) (K : ℕ) : LStack × ℚ → Op → Option (LStack × ℚ)
  | (st, a), .S x =>
      if 0 ≤ x ∧ x ≤ a - 1 then
        some (match st with
          | [] => ([(0, 1), (x, max x 1)], a - x)
          | (g, s) :: rest => ((0, s) :: (max g x, max x s) :: rest, a - x))
      else none
  | (st, a), .P j =>
      if 1 ≤ j ∧ j ≤ K ∧ j ≤ st.length then
        some (st.drop j, c * max a (max (frontQ (st.drop j))
          (lmaxQ ((st.take j).map Prod.fst ++ (st.take j).map Prod.snd))))
      else none

/-- Runs the ops; fails if an intermediate line is quantifier-free (normal form). -/
def runL (c : ℚ) (K : ℕ) : LStack × ℚ → List Op → Option (LStack × ℚ)
  | L, [] => some L
  | L, [o] => stepL c K L o
  | L, o :: o' :: os =>
      match stepL c K L o with
      | some L' => if L'.1 = [] then none else runL c K L' (o' :: os)
      | none => none

def checkL (c : ℚ) (K : ℕ) (a0 : ℚ) (ops : List Op) : Bool :=
  decide (1 ≤ a0) &&
    match runL c K ([], a0) ops with
    | some (st, a') => decide (st = []) && decide (a' < a0)
    | none => false

/-! ### Soundness into `QStep` -/

def castL (st : LStack) : List ℝ := st.map (fun p => ((p.2 : ℚ) : ℝ))

theorem lmaxQ_nonneg : ∀ l : List ℚ, 0 ≤ lmaxQ l
  | [] => le_rfl
  | _ :: l => le_trans (lmaxQ_nonneg l) (le_max_right _ _)

theorem lmaxQ_append_right : ∀ l m : List ℚ, lmaxQ m ≤ lmaxQ (l ++ m)
  | [], _ => le_rfl
  | _ :: l, m => le_trans (lmaxQ_append_right l m) (le_max_right _ _)

theorem lmax_cast_le : ∀ st : LStack, lmax (castL st) ≤ ((lmaxQ (st.map Prod.snd) : ℚ) : ℝ)
  | [] => by simp [castL, lmax, lmaxQ]
  | (g, s) :: st => by
      simp only [castL, List.map_cons, lmax, lmaxQ, Rat.cast_max] at *
      exact max_le_max le_rfl (lmax_cast_le st)

theorem front_cast_le (st : LStack) : front (castL st) ≤ ((frontQ st : ℚ) : ℝ) := by
  cases st with
  | nil => simp [castL, front, frontQ]
  | cons p st => simp [castL, front, frontQ]

theorem stepL_sound {c : ℚ} (hc : 0 ≤ c) {K : ℕ} {L L' : LStack × ℚ} {o : Op}
    (h : stepL c K L o = some L') :
    QStep (c : ℝ) K (castL L.1, (L.2 : ℝ)) (castL L'.1, (L'.2 : ℝ)) := by
  obtain ⟨st, a⟩ := L
  cases o with
  | S x =>
    simp only [stepL] at h
    split_ifs at h with hx
    obtain ⟨hx0, hxa⟩ := hx
    have hx0' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
    have hxa' : (x : ℝ) ≤ (a : ℝ) := by
      have : x ≤ a := by linarith
      exact_mod_cast this
    cases st with
    | nil =>
      simp only [Option.some.injEq] at h; subst h
      have := QStep.speed (c := (c : ℝ)) (k := K) [] (a : ℝ) (x : ℝ) (max (x : ℝ) 1) 1 ((a : ℝ) - x)
        hx0' hxa' (max_le_max le_rfl (by simp [front])) (by simp [front]) le_rfl
      simpa [castL, Rat.cast_max, Rat.cast_sub] using this
    | cons p rest =>
      obtain ⟨g, s⟩ := p
      simp only [Option.some.injEq] at h; subst h
      have := QStep.speed (c := (c : ℝ)) (k := K) ((s : ℝ) :: castL rest) (a : ℝ) (x : ℝ)
        (max (x : ℝ) s) s ((a : ℝ) - x) hx0' hxa' (by simp [front]) (by simp [front]) le_rfl
      simpa [castL, Rat.cast_max, Rat.cast_sub] using this
  | P j =>
    simp only [stepL] at h
    split_ifs at h with hj
    obtain ⟨hj1, hjK, hjl⟩ := hj
    simp only [Option.some.injEq] at h; subst h
    have hsplit : castL st = castL (st.take j) ++ castL (st.drop j) := by
      simp [castL, List.take_append_drop]
    have hlen : (castL (st.take j)).length = j := by
      simp [castL, List.length_take]; omega
    rw [hsplit]
    apply QStep.pop _ _ _ _ (by rw [hlen]; exact hj1) (by rw [hlen]; exact hjK)
    simp only [Rat.cast_mul, Rat.cast_max]
    apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hc)
    apply max_le_max le_rfl
    rw [max_comm]
    apply max_le_max
    · exact front_cast_le _
    · refine le_trans (lmax_cast_le _) ?_
      exact_mod_cast lmaxQ_append_right _ _

theorem runL_sound {c : ℚ} (hc : 0 ≤ c) {K : ℕ} :
    ∀ (ops : List Op) (L L' : LStack × ℚ), runL c K L ops = some L' →
      Relation.ReflTransGen (QStep (c : ℝ) K) (castL L.1, (L.2 : ℝ)) (castL L'.1, (L'.2 : ℝ))
  | [], L, L', h => by simp [runL] at h; subst h; exact Relation.ReflTransGen.refl
  | [o], L, L', h => by
      simp only [runL] at h
      exact Relation.ReflTransGen.single (stepL_sound hc h)
  | o :: o' :: os, L, L', h => by
      simp only [runL] at h
      cases hs : stepL c K L o with
      | none => rw [hs] at h; simp at h
      | some L'' =>
        rw [hs] at h
        simp only at h
        split_ifs at h
        exact Relation.ReflTransGen.head (stepL_sound hc hs) (runL_sound hc (o' :: os) L'' L' h)

/-- A checked certificate is a refutation in `QStep`: a path from DTS[n^{a0}] to DTS[n^{a'}],
a' < a0. -/
theorem checkL_sound {c : ℚ} (hc : 0 ≤ c) {K : ℕ} {a0 : ℚ} {ops : List Op}
    (h : checkL c K a0 ops = true) :
    ∃ a' : ℝ, a' < (a0 : ℝ) ∧ (0 : ℝ) ≤ a0 ∧
      Relation.ReflTransGen (QStep (c : ℝ) K) ([], (a0 : ℝ)) ([], a') := by
  simp only [checkL, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨ha0, hr⟩ := h
  cases hrun : runL c K ([], a0) ops with
  | none => rw [hrun] at hr; simp at hr
  | some L' =>
    rw [hrun] at hr
    obtain ⟨st, a'⟩ := L'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨hst, hlt⟩ := hr
    subst hst
    refine ⟨(a' : ℝ), by exact_mod_cast hlt, by exact_mod_cast (le_trans zero_le_one ha0), ?_⟩
    simpa [castL] using runL_sound hc ops ([], a0) ([], a') hrun

end PastaMath.QbfThreshold

end
