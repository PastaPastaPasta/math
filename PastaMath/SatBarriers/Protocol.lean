-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.Rule2

/-!
Protocol lines (perfect-completeness public-coin interaction read as alternation)
are dominated by tree speedups whenever the Merlin superscripts sum to at least the time saved.
-/

namespace PastaMath.SatBarriers
namespace PR

def PathStep (R : RLine → RLine → Prop) (L L' : RLine) : Prop :=
  ∃ (k : ℕ) (p : ℕ → RLine), 1 ≤ k ∧ p 0 = L ∧ p k = L' ∧ (∀ i < k, R (p i) (p (i + 1))) ∧
    (∀ i, 0 < i → i < k → (p i).1 ≠ [])

theorem path_single {R : RLine → RLine → Prop} {L L' : RLine} (h : R L L') : PathStep R L L' :=
  ⟨1, fun i => if i = 0 then L else L', le_rfl, by simp, by simp,
    fun i hi => by
      have : i = 0 := by omega
      subst this; simpa using h,
    fun i h1 h2 => absurd h2 (by omega)⟩

theorem path_trans {R : RLine → RLine → Prop} {L M L' : RLine} (h1 : PathStep R L M)
    (hM : M.1 ≠ []) (h2 : PathStep R M L') : PathStep R L L' := by
  obtain ⟨k, p, hk, hp0, hpk, hs, hne⟩ := h1
  obtain ⟨k', q, hk', hq0, hqk, hs', hne'⟩ := h2
  have key : ∀ i, k ≤ i → (if i ≤ k then p i else q (i - k)) = q (i - k) := by
    intro i hi
    by_cases h : i ≤ k
    · have : i = k := by omega
      subst this; simp [hpk, hq0]
    · simp [h]
  refine ⟨k + k', fun i => if i ≤ k then p i else q (i - k), by omega, by simp [hp0], ?_, ?_, ?_⟩
  · dsimp only; rw [key (k + k') (by omega)]; simpa using hqk
  · intro i hi
    rcases Nat.lt_or_ge i k with h | h
    · have e1 : i ≤ k := by omega
      have e2 : i + 1 ≤ k := by omega
      simp only [e1, e2, if_true]
      exact hs i h
    · dsimp only; rw [key i h, key (i + 1) (by omega)]
      have := hs' (i - k) (by omega)
      rwa [show i + 1 - k = i - k + 1 by omega]
  · intro i h1 h2
    rcases Nat.lt_or_ge i k with h | h
    · simp only [show i ≤ k by omega, if_true]
      exact hne i h1 h
    · dsimp only; rw [key i h]
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · subst h'; simpa [hq0] using hM
      · exact hne' (i - k) (by omega) (by omega)

theorem expand_prefix_path {R : RLine → RLine → Prop} {n : ℕ} {L : ℕ → RLine}
    (hstep : ∀ i < n, PathStep R (L i) (L (i + 1)))
    (hmid : ∀ i, 0 < i → i < n → (L i).1 ≠ []) :
    ∀ m ≤ n, ∃ (m' : ℕ) (g : ℕ → RLine), m ≤ m' ∧ (m = 0 → m' = 0) ∧ g 0 = L 0 ∧ g m' = L m ∧
      (∀ i < m', R (g i) (g (i + 1))) ∧ (∀ i, 0 < i → i < m' → (g i).1 ≠ []) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, fun _ => L 0, le_rfl, fun _ => rfl, rfl, rfl,
      fun i hi => absurd hi (by omega), fun i h1 h2 => absurd h2 (by omega)⟩
  | succ m ih =>
    intro hm
    obtain ⟨m', g, hle, hz, h0, hm', hs, hne⟩ := ih (by omega)
    obtain ⟨k, p, hk, hp0, hpk, hps, hpne⟩ := hstep m (by omega)
    have key : ∀ i, m' ≤ i → (if i ≤ m' then g i else p (i - m')) = p (i - m') := by
      intro i hi
      by_cases h : i ≤ m'
      · have : i = m' := by omega
        subst this; simp [hm', hp0]
      · simp [h]
    refine ⟨m' + k, fun i => if i ≤ m' then g i else p (i - m'), by omega, by omega, ?_, ?_, ?_, ?_⟩
    · simp [h0]
    · dsimp only; rw [key (m' + k) (by omega)]; simpa using hpk
    · intro i hi
      rcases Nat.lt_or_ge i m' with h | h
      · simp only [show i ≤ m' by omega, show i + 1 ≤ m' by omega, if_true]
        exact hs i h
      · dsimp only; rw [key i h, key (i + 1) (by omega)]
        have := hps (i - m') (by omega)
        rwa [show i + 1 - m' = i - m' + 1 by omega]
    · intro i h1 h2
      rcases Nat.lt_or_ge i m' with h | h
      · simp only [show i ≤ m' by omega, if_true]
        exact hne i h1 h
      · dsimp only; rw [key i h]
        rcases Nat.eq_or_lt_of_le h with h' | h'
        · subst h'
          have hmpos : 0 < m := by
            rcases Nat.eq_zero_or_pos m with e | e
            · exact absurd (hz e) (by omega)
            · exact e
          simpa [hp0] using hmid m hmpos (by omega)
        · exact hpne (i - m') (by omega) (by omega)

theorem refutes_expand_path {R : RLine → RLine → Prop} {n : ℕ} {L : ℕ → RLine}
    (h : RefutesWith (PathStep R) n L) : ∃ (n' : ℕ) (g : ℕ → RLine), RefutesWith R n' g := by
  obtain ⟨hn, h0, hN, ha, hlt, hstep, hmid⟩ := h
  obtain ⟨m', g, hle, -, hg0, hgm, hs, hne⟩ := expand_prefix_path hstep hmid n le_rfl
  exact ⟨m', g, by omega, by rw [hg0]; exact h0, by rw [hgm]; exact hN, by rw [hg0]; exact ha,
    by rw [hgm, hg0]; exact hlt, hs, hne⟩

/-- Flatten protocol rounds (Merlin superscript, coin superscript) into a block list. -/
def flat : List (ℝ × ℝ) → List ℝ
  | [] => []
  | (m, r) :: t => m :: r :: flat t

def exactRounds (b : ℝ) (xs : List ℝ) : List (ℝ × ℝ) := xs.map fun x => (max x b, b)

theorem tree_path (c β b : ℝ) (hb : 0 ≤ b) :
    ∀ (xs P : List ℝ) (a : ℝ), xs ≠ [] → (∀ x ∈ xs, 0 ≤ x) → xs.sum ≤ a →
      PathStep (Step c β) (P ++ [b], a) (P ++ b :: flat (exactRounds b xs), a - xs.sum) := by
  intro xs
  induction xs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons x t ih =>
    intro P a _ hx hs
    have hx0 : 0 ≤ x := hx x (by simp)
    have ht0 : ∀ y ∈ t, 0 ≤ y := fun y hy => hx y (by simp [hy])
    have hts : 0 ≤ t.sum := List.sum_nonneg ht0
    have hsum : (x :: t).sum = x + t.sum := List.sum_cons
    have hxa : x ≤ a := by linarith
    have ha : 0 ≤ a := by linarith
    have two : PathStep (Step c β) (P ++ [b], a) (P ++ [b, max x b, b], a - x) :=
      path_trans (path_single (dummy_step c β P b a hb ha)) (by simp)
        (path_single (rule2_second c β P b a x hx0 hxa))
    rcases t with _ | ⟨y, t'⟩
    · simpa [exactRounds, flat] using two
    · have hrest := ih (P ++ [b, max x b]) (a - x) (by simp) ht0 (by linarith)
      have e1 : (P ++ [b, max x b]) ++ [b] = P ++ [b, max x b, b] := by simp
      rw [e1] at hrest
      have e2 : (P ++ [b, max x b]) ++ b :: flat (exactRounds b (y :: t')) =
          P ++ b :: flat (exactRounds b (x :: y :: t')) := by
        simp [exactRounds, flat]
      have e3 : a - x - (y :: t').sum = a - (x :: y :: t').sum := by
        rw [hsum]; ring
      rw [e2, e3] at hrest
      exact path_trans two (by simp) hrest

theorem getD_le_of_forall₂ : ∀ {l l' : List ℝ}, List.Forall₂ (· ≤ ·) l l' →
    ∀ i, l.getD i 0 ≤ l'.getD i 0
  | [], [], .nil, i => by simp
  | _ :: _, _ :: _, .cons h t, i => by
    cases i with
    | zero => simpa using h
    | succ i => simpa using getD_le_of_forall₂ t i

theorem forall₂_refl_append (P : List ℝ) {l l' : List ℝ} (h : List.Forall₂ (· ≤ ·) l l') :
    List.Forall₂ (· ≤ ·) (P ++ l) (P ++ l') := by
  induction P with
  | nil => simpa using h
  | cons a P ih => exact List.Forall₂.cons le_rfl ih

theorem forall₂_flat (b : ℝ) : ∀ {xs : List ℝ} {rs : List (ℝ × ℝ)},
    List.Forall₂ (fun x p => max x b ≤ p.1 ∧ b ≤ p.2) xs rs →
    List.Forall₂ (· ≤ ·) (flat (exactRounds b xs)) (flat rs)
  | [], [], .nil => by simp [exactRounds, flat]
  | _ :: _, (m, r) :: _, .cons h t => by
    simp only [exactRounds, List.map_cons, flat] at *
    exact List.Forall₂.cons h.1 (List.Forall₂.cons h.2 (forall₂_flat b t))

theorem greedy (b : ℝ) (hb : 0 ≤ b) : ∀ (rs : List (ℝ × ℝ)) (a : ℝ), 0 ≤ a →
    (∀ p ∈ rs, b ≤ p.1 ∧ b ≤ p.2) →
    ∃ xs : List ℝ, List.Forall₂ (fun x p => 0 ≤ x ∧ max x b ≤ p.1 ∧ b ≤ p.2) xs rs ∧
      xs.sum = min (rs.map Prod.fst).sum a
  | [], a, ha, _ => ⟨[], .nil, by simp [ha]⟩
  | (m, r) :: t, a, ha, hp => by
    have hmr : b ≤ m ∧ b ≤ r := hp (m, r) (by simp)
    have hm : 0 ≤ m := le_trans hb hmr.1
    have ht : ∀ p ∈ t, b ≤ p.1 ∧ b ≤ p.2 := fun p h => hp p (by simp [h])
    have hts : 0 ≤ (t.map Prod.fst).sum := List.sum_nonneg (by
      intro y hy
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hy
      exact le_trans hb (ht p hp').1)
    obtain ⟨xs, hxs, hsum⟩ := greedy b hb t (a - min m a) (by
      have := min_le_right m a; linarith) ht
    refine ⟨min m a :: xs, List.Forall₂.cons
      ⟨le_min hm ha, max_le (min_le_left _ _) hmr.1, hmr.2⟩ hxs, ?_⟩
    simp only [List.sum_cons, List.map_cons, hsum]
    rcases le_total m a with h | h
    · rw [min_eq_left h]
      rcases le_total (t.map Prod.fst).sum (a - m) with h' | h'
      · rw [min_eq_left h', min_eq_left (by linarith)]
      · rw [min_eq_right h', min_eq_right (by linarith)]; ring
    · rw [min_eq_right h, sub_self, min_eq_right hts, min_eq_right (by linarith)]; ring

/-- The reduced form of a perfect-completeness public-coin protocol line below a block of
superscript `b`: either the first Merlin block is a new block (first disjunct of the output)
or it merges into the innermost block (second disjunct). Every block passes the input
(`b ≤`), and the Merlin superscripts sum to at least the time saved `a - v`. -/
def ProtoStep (c β : ℝ) (L L' : RLine) : Prop :=
  Step c β L L' ∨
  ∃ (P : List ℝ) (b a v : ℝ) (rs : List (ℝ × ℝ)), L = (P ++ [b], a) ∧
    (L' = (P ++ b :: flat rs, v) ∨ L' = (P ++ flat rs, v)) ∧
    0 ≤ b ∧ 0 ≤ a ∧ 0 ≤ v ∧ rs ≠ [] ∧ (∀ p ∈ rs, b ≤ p.1 ∧ b ≤ p.2) ∧
    a - v ≤ (rs.map Prod.fst).sum

theorem weak_of_forall₂ (c β : ℝ) {l l' : List ℝ} (a a' : ℝ) (h : List.Forall₂ (· ≤ ·) l l')
    (ha : a ≤ a') : Step c β (l, a) (l', a') :=
  Step.weak l l' a a' h.length_eq.symm (getD_le_of_forall₂ h) ha

theorem merged_path (c β b : ℝ) (hb : 0 ≤ b) (P : List ℝ) (a : ℝ) (x : ℝ) (t : List ℝ)
    (hx : 0 ≤ x) (ht : ∀ y ∈ t, 0 ≤ y) (hs : x + t.sum ≤ a) :
    PathStep (Step c β) (P ++ [b], a) (P ++ flat (exactRounds b (x :: t)), a - (x + t.sum)) := by
  have hts : 0 ≤ t.sum := List.sum_nonneg ht
  have first : Step c β (P ++ [b], a) (P ++ [max x b, b], a - x) :=
    Step.speed P b a x (max x b) b (a - x) hx (by linarith) le_rfl le_rfl le_rfl
  rcases t with _ | ⟨y, t'⟩
  · simpa [exactRounds, flat] using path_single first
  · have hrest := tree_path c β b hb (y :: t') (P ++ [max x b]) (a - x) (by simp) ht
      (by linarith)
    have e1 : (P ++ [max x b]) ++ [b] = P ++ [max x b, b] := by simp
    have e2 : (P ++ [max x b]) ++ b :: flat (exactRounds b (y :: t')) =
        P ++ flat (exactRounds b (x :: y :: t')) := by simp [exactRounds, flat]
    rw [e1, e2, show a - x - (y :: t').sum = a - (x + (y :: t').sum) by ring] at hrest
    exact path_trans (path_single first) (by simp) hrest

theorem forall₂_left {Q : ℝ → ℝ × ℝ → Prop} : ∀ {xs : List ℝ} {rs : List (ℝ × ℝ)},
    List.Forall₂ Q xs rs → (∀ x p, Q x p → 0 ≤ x) → ∀ x ∈ xs, 0 ≤ x
  | [], [], .nil, _ => by simp
  | _ :: _, _ :: _, .cons h t, hQ => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hQ _ _ h
    · exact forall₂_left t hQ x hx

theorem proto_path (c β : ℝ) {L L' : RLine} (h : ProtoStep c β L L') :
    PathStep (Step c β) L L' := by
  rcases h with h | ⟨P, b, a, v, rs, rfl, hL', hb, ha, hv, hne, hbnd, hsum⟩
  · exact path_single h
  obtain ⟨xs, hxs, hxsum⟩ := greedy b hb rs a ha hbnd
  have hxs0 : ∀ x ∈ xs, 0 ≤ x := forall₂_left hxs (fun _ _ h => h.1)
  have hxsne : xs ≠ [] := by
    intro e; subst e; cases hxs; exact hne rfl
  have hle : xs.sum ≤ a := by rw [hxsum]; exact min_le_right _ _
  have hfin : a - xs.sum ≤ v := by
    rw [hxsum]
    rcases le_total (rs.map Prod.fst).sum a with h' | h'
    · rw [min_eq_left h']; linarith
    · rw [min_eq_right h']; linarith
  have hF : List.Forall₂ (fun x p => max x b ≤ p.1 ∧ b ≤ p.2) xs rs :=
    List.Forall₂.imp (fun _ _ hxp => hxp.2) hxs
  have hflat := forall₂_flat b hF
  rcases hL' with rfl | rfl
  · have hp := tree_path c β b hb xs P a hxsne hxs0 hle
    exact path_trans hp (by simp) (path_single (weak_of_forall₂ c β _ _
      (forall₂_refl_append P (List.Forall₂.cons le_rfl hflat)) hfin))
  · obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hxsne
    have hx0 : 0 ≤ x := hxs0 x (by simp)
    have ht0 : ∀ y ∈ t, 0 ≤ y := fun y hy => hxs0 y (by simp [hy])
    have hs : x + t.sum ≤ a := by simpa [List.sum_cons] using hle
    have hp := merged_path c β b hb P a x t hx0 ht0 hs
    refine path_trans hp ?_ (path_single (weak_of_forall₂ c β _ _
      (forall₂_refl_append P hflat) (by simpa [List.sum_cons] using hfin)))
    simp [exactRounds, flat]

theorem no_refutation_proto {c β : ℝ} (hc : r7 ≤ c) (hβ : 1 / (r7 * (r7 - 1)) ≤ β) (n : ℕ)
    (L : ℕ → RLine) : ¬ RefutesWith (ProtoStep c β) n L := by
  intro h
  have h' : RefutesWith (PathStep (Step c β)) n L := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨h1, h2, h3, h4, h5, fun i hi => proto_path c β (h6 i hi), h7⟩
  obtain ⟨n', g, hg⟩ := refutes_expand_path h'
  exact no_refutation hc hβ n' g hg

theorem proto_witness :
    ProtoStep (9 / 5) 1 ([0, 1], 3) ([0, 1, 1, 1, 1, 1], 1) ∧
      ¬ Step (9 / 5) 1 ([0, 1], 3) ([0, 1, 1, 1, 1, 1], 1) := by
  refine ⟨Or.inr ⟨[0], 1, 3, 1, [(1, 1), (1, 1)], rfl, Or.inl rfl, by norm_num, by norm_num,
    by norm_num, by simp, by simp, by norm_num⟩, ?_⟩
  intro h
  have := step_len h
  simp at this

end PR
end PastaMath.SatBarriers
