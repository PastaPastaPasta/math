-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Derivation

namespace PastaMath.SatBarriers

theorem dummy_step (c β : ℝ) (bs : List ℝ) (b a : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) :
    Step c β (bs ++ [b], a) (bs ++ [b, b], a) :=
  Step.speed bs b a 0 b b a le_rfl ha (by simp [hb]) le_rfl (by linarith)

theorem rule2_second (c β : ℝ) (bs : List ℝ) (b a x : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a) :
    Step c β (bs ++ [b, b], a) (bs ++ [b, max x b, b], a - x) := by
  have h := Step.speed (c := c) (β := β) (bs ++ [b]) b a x (max x b) b (a - x) hx hxa le_rfl le_rfl
    le_rfl
  simpa [List.append_assoc] using h

def Rule2Step (c β : ℝ) (L L' : RLine) : Prop :=
  Step c β L L' ∨ ∃ M : RLine, M.1 ≠ [] ∧ Step c β L M ∧ Step c β M L'

theorem rule2_is_rule2step (c β : ℝ) (bs : List ℝ) (b a x : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hx : 0 ≤ x) (hxa : x ≤ a) :
    Rule2Step c β (bs ++ [b], a) (bs ++ [b, max x b, b], a - x) :=
  Or.inr ⟨(bs ++ [b, b], a), by simp, dummy_step c β bs b a hb ha, rule2_second c β bs b a x hx hxa⟩

theorem expand_prefix {c β : ℝ} {n : ℕ} {L : ℕ → RLine} (hstep : ∀ i < n, Rule2Step c β (L i) (L (i + 1)))
    (hmid : ∀ i, 0 < i → i < n → (L i).1 ≠ []) :
    ∀ m ≤ n, ∃ (m' : ℕ) (g : ℕ → RLine), m ≤ m' ∧ (m = 0 → m' = 0) ∧ g 0 = L 0 ∧ g m' = L m ∧
      (∀ i < m', Step c β (g i) (g (i + 1))) ∧ (∀ i, 0 < i → i < m' → (g i).1 ≠ []) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, fun _ => L 0, le_rfl, fun _ => rfl, rfl, rfl,
      fun i hi => absurd hi (by omega), fun i h1 h2 => absurd h2 (by omega)⟩
  | succ m ih =>
    intro hm
    obtain ⟨m', g, hle, hz, h0, hm', hs, hne⟩ := ih (by omega)
    have hLm : 0 < m → (L m).1 ≠ [] := fun h => hmid m h (by omega)
    have hgm' : 0 < m' → (g m').1 ≠ [] := by
      intro hpos
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (hz h) (by omega)
      · rw [hm']; exact hLm h
    rcases hstep m (by omega) with hS | ⟨M, hM, hS1, hS2⟩
    · refine ⟨m' + 1, fun i => if i ≤ m' then g i else L (m + 1), by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp [h0]
      · simp
      · intro i hi
        rcases Nat.lt_or_ge i m' with h | h
        · have e1 : i ≤ m' := by omega
          have e2 : i + 1 ≤ m' := by omega
          simp only [e1, e2, if_true]
          exact hs i h
        · have hi' : i = m' := by omega
          subst hi'
          simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false]
          rw [hm']; exact hS
      · intro i h1 h2
        have e1 : i ≤ m' := by omega
        simp only [e1, if_true]
        rcases Nat.lt_or_ge i m' with h | h
        · exact hne i h1 h
        · have hi' : i = m' := by omega
          subst hi'
          exact hgm' h1
    · refine ⟨m' + 2, fun i => if i ≤ m' then g i else if i = m' + 1 then M else L (m + 1),
        by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp [h0]
      · simp
      · intro i hi
        rcases Nat.lt_or_ge i m' with h | h
        · have e1 : i ≤ m' := by omega
          have e2 : i + 1 ≤ m' := by omega
          simp only [e1, e2, if_true]
          exact hs i h
        · rcases Nat.lt_or_ge i (m' + 1) with h' | h'
          · have hi' : i = m' := by omega
            subst hi'
            simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false]
            rw [hm']; exact hS1
          · have hi' : i = m' + 1 := by omega
            subst hi'
            simp only [show ¬ (m' + 1 ≤ m') by omega, if_false, if_true,
              show ¬ (m' + 1 + 1 ≤ m') by omega, show ¬ (m' + 1 + 1 = m' + 1) by omega]
            exact hS2
      · intro i h1 h2
        rcases Nat.lt_or_ge i m' with h | h
        · have e1 : i ≤ m' := by omega
          simp only [e1, if_true]
          exact hne i h1 h
        · rcases Nat.lt_or_ge i (m' + 1) with h' | h'
          · have hi' : i = m' := by omega
            subst hi'
            simp only [le_refl, if_true]
            exact hgm' h1
          · have hi' : i = m' + 1 := by omega
            subst hi'
            simp only [show ¬ (m' + 1 ≤ m') by omega, if_false, if_true]
            exact hM

theorem refutes_expand {c β : ℝ} {n : ℕ} {L : ℕ → RLine} (h : RefutesWith (Rule2Step c β) n L) :
    ∃ (n' : ℕ) (g : ℕ → RLine), RefutesWith (Step c β) n' g := by
  obtain ⟨hn, h0, hN, ha, hlt, hstep, hmid⟩ := h
  obtain ⟨m', g, hle, -, hg0, hgm, hs, hne⟩ := expand_prefix hstep hmid n le_rfl
  refine ⟨m', g, by omega, by rw [hg0]; exact h0, by rw [hgm]; exact hN, by rw [hg0]; exact ha,
    by rw [hgm, hg0]; exact hlt, hs, hne⟩

theorem no_refutation_rule2 {c β : ℝ} (hc : r7 ≤ c) (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (n : ℕ)
    (L : ℕ → RLine) : ¬ RefutesWith (Rule2Step c β) n L := by
  intro h
  obtain ⟨n', g, hg⟩ := refutes_expand h
  exact no_refutation hc hβ n' g hg

end PastaMath.SatBarriers
