-- SPDX-License-Identifier: Apache-2.0
import PastaMath.SatBarriers.LocalizedMax

namespace PastaMath.SatBarriers

/-!
Concrete reduced semantics of R1L, R1T and C1L, with the array exponents represented by
`κ : Option ℝ` (`none` when no arrays exist, `some k` when arrays exist with maximum exponent `k`).
This is exact, because every formula of the lemmas uses the arrays only through
`max_ℓ (κ_ℓ + common term)` (omitting the array term when no arrays exist). We prove that every
concrete step maps to an `LStepX c 1` step under the abstraction `ℓ := optMax e_u κ`, and that
concrete refutations cannot exist for `c ≥ 2cos(π/7)`.
-/

/-- Maximum of `eu` and the optional array exponent `κ` (`eu` when no arrays exist). -/
def optMax (eu : ℝ) : Option ℝ → ℝ
  | none => eu
  | some k => max eu k

/-- `max eu (k + Δ)` when arrays exist (`some k`), or `eu` when no arrays exist (`none`). -/
def optAdd (eu : ℝ) (κ : Option ℝ) (Δ : ℝ) : ℝ :=
  match κ with
  | none => eu
  | some k => max eu (k + Δ)

theorem le_optMax (eu : ℝ) (κ : Option ℝ) : eu ≤ optMax eu κ := by
  cases κ <;> simp [optMax]

theorem le_optAdd (eu : ℝ) (κ : Option ℝ) (Δ : ℝ) : eu ≤ optAdd eu κ Δ := by
  cases κ <;> simp [optAdd]

theorem optMax_le_optAdd {eu Δ : ℝ} (hΔ : 0 ≤ Δ) (κ : Option ℝ) :
    optMax eu κ ≤ optAdd eu κ Δ := by
  cases κ with
  | none => exact le_rfl
  | some k => exact max_le_max le_rfl (by linarith)

theorem optAdd_mono {eu Δ₁ Δ₂ : ℝ} (h : Δ₁ ≤ Δ₂) (κ : Option ℝ) :
    optAdd eu κ Δ₁ ≤ optAdd eu κ Δ₂ := by
  cases κ with
  | none => exact le_rfl
  | some k => exact max_le_max le_rfl (by linarith)

structure CBlk where
  sup : ℝ
  x : ℝ
  σ : ℝ
  p : ℝ
  κ : Option ℝ
  eu : ℝ

structure CDesc where
  p : ℝ
  κ : Option ℝ
  eu : ℝ

abbrev CLine := List CBlk × ℝ × CDesc

/-- Bound on the parent superscript recorded by a block's creation data (invariant J at
creation time, together with the speedup's own x). -/
def gCre (B : CBlk) : ℝ := max B.x (optAdd B.eu B.κ (B.x + B.σ - B.p))

def okRest : ℝ → List CBlk → Prop
  | _, [] => True
  | s, C :: rest => s ≤ gCre C ∧ okRest C.sup rest

def okChain : List CBlk → Prop
  | [] => True
  | B :: rest => B.x = 0 ∧ B.eu = 0 ∧ B.κ = none ∧ okRest B.sup rest

def lastSup (s : ℝ) : List CBlk → ℝ
  | [] => s
  | C :: rest => lastSup C.sup rest

def ctop : List CBlk → ℝ
  | [] => 0
  | B :: rest => lastSup B.sup rest

def CInv (L : CLine) : Prop :=
  okChain L.1 ∧ (∀ B ∈ L.1, 0 ≤ B.sup ∧ 0 ≤ B.x ∧ 0 ≤ B.eu) ∧
    0 ≤ L.2.1 ∧ 0 ≤ L.2.2.eu ∧
    ctop L.1 ≤ optAdd L.2.2.eu L.2.2.κ (L.2.1 - L.2.2.p)

/-- Window of C1L's chunk instance: `max(y, eu, κ + max(0, y + σ − p))` (array term omitted
when `κ = none`). -/
def cDelta (B : CBlk) (y : ℝ) : ℝ := max y (optAdd B.eu B.κ (max 0 (y + B.σ - B.p)))

/-- Updated array exponent after C1L: `y` if no prior arrays existed, else
`max(k + max(0, y + σ − p), y)`. -/
def nextKappa (B : CBlk) (y : ℝ) : ℝ :=
  match B.κ with
  | none => y
  | some k => max (k + max 0 (y + B.σ - B.p)) y

inductive LocsStep (c : ℝ) : CLine → CLine → Prop
  | init (d : ℝ) (D : CDesc) : LocsStep c ([], d, D) ([⟨0, 0, 0, 0, none, 0⟩], d, D)
  | r1l (bs : List CBlk) (B : CBlk) (d : ℝ) (D : CDesc) (x p' : ℝ) (hx : 0 ≤ x) (hxd : x ≤ d)
      (hp' : p' ≤ min D.p (d - x)) :
      LocsStep c (bs ++ [B], d, D)
        (bs ++ [⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩,
          ⟨optAdd D.eu D.κ (max 0 (d - x - D.p)), x, d - x, D.p, D.κ, D.eu⟩],
          d - x, ⟨p', D.κ, D.eu⟩)
  | r1t (bs : List CBlk) (B : CBlk) (d : ℝ) (D : CDesc) (x : ℝ) (hx : 0 ≤ x) (hxd : x ≤ d) :
      LocsStep c (bs ++ [B], d, D)
        (bs ++ [⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩, ⟨d - x, x, d - x, D.p, D.κ, D.eu⟩],
          d - x, ⟨0, some 0, 0⟩)
  | c1l (bs : List CBlk) (B : CBlk) (t : ℝ) (D : CDesc) (y p'' : ℝ) (hbs : bs ≠ [])
      (hy : 0 ≤ y) (hyx : y ≤ B.x) (hp : c * max (cDelta B y) (max B.sup t) ≤ p'') :
      LocsStep c (bs ++ [B], t, D)
        (bs, B.x - y + p'', ⟨p'', some (nextKappa B y), B.eu⟩)
  | top (B : CBlk) (t e : ℝ) (D D' : CDesc) (he : c * max B.sup t ≤ e) (hD : 0 ≤ D'.eu) :
      LocsStep c ([B], t, D) ([], e, D')

def absB (B : CBlk) : LBlock := (B.sup, B.x, optMax B.eu B.κ)

def absL (L : CLine) : LLine := (L.1.map absB, L.2.1, optMax L.2.2.eu L.2.2.κ)

/-- A concrete refutation from the initial machine (`e_u = 0`, `κ = none`, i.e., no arrays). -/
def LocsRefutes (c : ℝ) (n : ℕ) (L : ℕ → CLine) : Prop :=
  1 ≤ n ∧ (L 0).1 = [] ∧ (L 0).2.2.eu = 0 ∧ (L 0).2.2.κ = none ∧ (L n).1 = [] ∧
    0 ≤ (L 0).2.1 ∧ (L n).2.1 < (L 0).2.1 ∧ (∀ i < n, LocsStep c (L i) (L (i + 1))) ∧
    (∀ i, 0 < i → i < n → (L i).1 ≠ [])

theorem lastSup_append (s : ℝ) (l : List CBlk) (B : CBlk) : lastSup s (l ++ [B]) = B.sup := by
  induction l generalizing s with
  | nil => rfl
  | cons C rest ih => exact ih C.sup

theorem okRest_append (s : ℝ) (l : List CBlk) (B : CBlk) :
    okRest s (l ++ [B]) ↔ okRest s l ∧ lastSup s l ≤ gCre B := by
  induction l generalizing s with
  | nil => simp [okRest, lastSup]
  | cons C rest ih =>
    simp only [List.cons_append, okRest, lastSup]
    rw [ih C.sup]
    tauto

theorem ctop_append (l : List CBlk) (B : CBlk) : ctop (l ++ [B]) = B.sup := by
  cases l with
  | nil => rfl
  | cons C rest => simp only [List.cons_append, ctop]; exact lastSup_append _ _ _

theorem okChain_parent {bs : List CBlk} {B : CBlk} (h : okChain (bs ++ [B])) (hbs : bs ≠ []) :
    okChain bs ∧ ctop bs ≤ gCre B := by
  cases bs with
  | nil => exact absurd rfl hbs
  | cons C rest =>
    simp only [List.cons_append, okChain] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [okRest_append] at h4
    exact ⟨⟨h1, h2, h3, h4.1⟩, h4.2⟩

theorem okChain_snoc {bs : List CBlk} {B : CBlk} (h : okChain bs) (hbs : bs ≠ [])
    (hB : ctop bs ≤ gCre B) : okChain (bs ++ [B]) := by
  cases bs with
  | nil => exact absurd rfl hbs
  | cons C rest =>
    simp only [List.cons_append, okChain] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, h3, ?_⟩
    rw [okRest_append]
    exact ⟨h4, hB⟩

/-- Changing only the sup of the innermost block keeps the chain condition. -/
theorem okChain_set_last {bs : List CBlk} {B : CBlk} (s : ℝ) (h : okChain (bs ++ [B])) :
    okChain (bs ++ [⟨s, B.x, B.σ, B.p, B.κ, B.eu⟩]) := by
  cases bs with
  | nil => simp only [List.nil_append, okChain, okRest] at h ⊢; exact ⟨h.1, h.2.1, h.2.2.1, trivial⟩
  | cons C rest =>
    simp only [List.cons_append, okChain] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, h3, ?_⟩
    rw [okRest_append] at h4 ⊢
    exact ⟨h4.1, by simpa [gCre] using h4.2⟩

theorem ltop_map_absB (bs : List CBlk) : ltop (bs.map absB) = ctop bs := by
  rcases List.eq_nil_or_concat bs with h | ⟨L, b, h⟩
  · subst h; simp [ltop, lsup, ctop]
  · subst h
    rw [List.concat_eq_append, List.map_append, List.map_singleton, ltop_app, ctop_append]
    rfl

theorem optMax_nextKappa (B : CBlk) (y : ℝ) :
    optMax B.eu (some (nextKappa B y)) = cDelta B y := by
  cases hκ : B.κ with
  | none =>
    simp only [optMax, nextKappa, cDelta, optAdd, hκ, max_comm]
  | some k =>
    simp only [optMax, nextKappa, cDelta, optAdd, hκ]
    rw [max_comm y _, max_assoc, max_comm _ y, ← max_assoc]

theorem locs_embed {c : ℝ} (hc : 1 ≤ c) {L L' : CLine} (hI : CInv L) (h : LocsStep c L L') :
    LStepX c 1 (absL L) (absL L') ∧ CInv L' := by
  obtain ⟨hok, hnn, hd, heu, hJ⟩ := hI
  cases h with
  | init d D =>
    refine ⟨?_, ?_⟩
    · have := LStepX.init (c := c) (β := 1) d (optMax D.eu D.κ)
      simpa [absL, absB, optMax] using this
    · refine ⟨?_, ?_, hd, heu, ?_⟩
      · simp [okChain, okRest]
      · intro B hB; simp at hB; subst hB; simp
      · simp only [ctop, lastSup]
        exact le_trans heu (le_optAdd D.eu D.κ _)
  | r1l bs B d D x p' hx hxd hp' =>
    have hBnn := hnn B (by simp)
    refine ⟨?_, ?_⟩
    · have := LStepX.speed (c := c) (β := 1) (bs.map absB) B.sup B.x (optMax B.eu B.κ) d
        (optMax D.eu D.κ) x (max B.sup x) (optAdd D.eu D.κ (max 0 (d - x - D.p))) (d - x) hx hxd
        (by rw [max_comm]) (optMax_le_optAdd (le_max_left _ _) D.κ) le_rfl
      simpa [absL, absB, List.map_append] using this
    · refine ⟨?_, ?_, by linarith, heu, ?_⟩
      · have h1 := okChain_set_last (max B.sup x) hok
        have hne : bs ++ [(⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩ : CBlk)] ≠ [] := by simp
        have h2 := okChain_snoc h1 hne (B := ⟨optAdd D.eu D.κ (max 0 (d - x - D.p)), x, d - x, D.p,
          D.κ, D.eu⟩)
        rw [ctop_append] at h2
        have : bs ++ [(⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩ : CBlk),
            ⟨optAdd D.eu D.κ (max 0 (d - x - D.p)), x, d - x, D.p, D.κ, D.eu⟩] =
            (bs ++ [⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩]) ++
              [⟨optAdd D.eu D.κ (max 0 (d - x - D.p)), x, d - x, D.p, D.κ, D.eu⟩] := by simp
        rw [this]
        apply h2
        rw [ctop_append] at hJ
        simp only [gCre]
        apply max_le _ (le_max_left _ _)
        apply le_trans hJ
        apply le_trans _ (le_max_right _ _)
        exact optAdd_mono (by linarith) D.κ
      · intro C hC
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hC
        rcases hC with hC | hC | hC
        · exact hnn C (by simp [hC])
        · subst hC; exact ⟨le_trans hBnn.1 (le_max_left _ _), hBnn.2.1, hBnn.2.2⟩
        · subst hC; exact ⟨le_trans heu (le_optAdd D.eu D.κ _), hx, heu⟩
      · rw [show bs ++ [(⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩ : CBlk),
            ⟨optAdd D.eu D.κ (max 0 (d - x - D.p)), x, d - x, D.p, D.κ, D.eu⟩] =
            (bs ++ [⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩]) ++
              [⟨optAdd D.eu D.κ (max 0 (d - x - D.p)), x, d - x, D.p, D.κ, D.eu⟩] by simp,
          ctop_append]
        have hle : max 0 (d - x - D.p) ≤ d - x - p' := by
          have h1 := le_trans hp' (min_le_left _ _)
          have h2 := le_trans hp' (min_le_right _ _)
          exact max_le (by linarith) (by linarith)
        exact optAdd_mono hle D.κ
  | r1t bs B d D x hx hxd =>
    have hBnn := hnn B (by simp)
    refine ⟨?_, ?_⟩
    · have := LStepX.speedT (c := c) (β := 1) (bs.map absB) B.sup B.x (optMax B.eu B.κ) d
        (optMax D.eu D.κ) x (max B.sup x) (d - x) (d - x) (optMax 0 (some 0)) hx hxd
        (by rw [max_comm]) le_rfl le_rfl (by simp [optMax])
      simpa [absL, absB, List.map_append] using this
    · refine ⟨?_, ?_, by linarith, le_rfl, ?_⟩
      · have h1 := okChain_set_last (max B.sup x) hok
        have hne : bs ++ [(⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩ : CBlk)] ≠ [] := by simp
        have h2 := okChain_snoc h1 hne (B := ⟨d - x, x, d - x, D.p, D.κ, D.eu⟩)
        rw [ctop_append] at h2
        have : bs ++ [(⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩ : CBlk), ⟨d - x, x, d - x, D.p, D.κ, D.eu⟩] =
            (bs ++ [⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩]) ++ [⟨d - x, x, d - x, D.p, D.κ, D.eu⟩] := by
          simp
        rw [this]
        apply h2
        rw [ctop_append] at hJ
        simp only [gCre]
        apply max_le _ (le_max_left _ _)
        apply le_trans hJ
        apply le_trans _ (le_max_right _ _)
        exact optAdd_mono (by linarith) D.κ
      · intro C hC
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hC
        rcases hC with hC | hC | hC
        · exact hnn C (by simp [hC])
        · subst hC; exact ⟨le_trans hBnn.1 (le_max_left _ _), hBnn.2.1, hBnn.2.2⟩
        · subst hC; exact ⟨by linarith, hx, heu⟩
      · rw [show bs ++ [(⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩ : CBlk), ⟨d - x, x, d - x, D.p, D.κ, D.eu⟩] =
            (bs ++ [⟨max B.sup x, B.x, B.σ, B.p, B.κ, B.eu⟩]) ++ [⟨d - x, x, d - x, D.p, D.κ, D.eu⟩] by
            simp, ctop_append]
        simp [optAdd]
  | c1l bs B t D y p'' hbs hy hyx hp =>
    have hBnn := hnn B (by simp)
    obtain ⟨hokP, hX⟩ := okChain_parent hok hbs
    have hc0 : (0 : ℝ) ≤ c := by linarith
    set δ := cDelta B y with hδ
    set m := max (max B.sup t) (optMax B.eu B.κ) with hm
    have hδy : y ≤ δ := le_max_left _ _
    have hδopt : optMax B.eu B.κ ≤ δ :=
      le_trans (optMax_le_optAdd (le_max_left _ _) B.κ) (le_max_right _ _)
    have hmM : m ≤ max δ (max B.sup t) :=
      max_le (le_max_right _ _) (le_trans hδopt (le_max_left _ _))
    have hM0 : 0 ≤ max δ (max B.sup t) := le_trans hBnn.1 (le_trans (le_max_left _ _) (le_max_right _ _))
    have hfloor : ctop bs ≤ B.x - y + δ := by
      apply le_trans hX
      simp only [gCre]
      apply max_le (by linarith)
      cases hκ : B.κ with
      | none =>
        simp only [optAdd]
        have h1 : B.eu ≤ δ := by
          rw [hδ]; simp only [cDelta, optAdd, hκ]; exact le_max_right _ _
        linarith
      | some k =>
        simp only [optAdd]
        have h1 : B.eu ≤ δ := by
          rw [hδ]; simp only [cDelta, optAdd, hκ]; exact le_trans (le_max_left _ _) (le_max_right _ _)
        have h2 : k + max 0 (y + B.σ - B.p) ≤ δ := by
          rw [hδ]; simp only [cDelta, optAdd, hκ]; exact le_trans (le_max_right _ _) (le_max_right _ _)
        apply max_le (by linarith)
        have : k + (B.x + B.σ - B.p) ≤ B.x - y + (k + max 0 (y + B.σ - B.p)) := by
          linarith [le_max_right 0 (y + B.σ - B.p)]
        linarith
    have hl' : optMax B.eu (some (nextKappa B y)) = δ := optMax_nextKappa B y
    refine ⟨?_, ?_⟩
    · have hkey : c * m ≤ p'' := le_trans (mul_le_mul_of_nonneg_left hmM hc0) hp
      have := LStepX.slow (c := c) (β := 1) (bs.map absB) B.sup B.x (optMax B.eu B.κ) t
        (optMax D.eu D.κ) (B.x - y + p'') (optMax B.eu (some (nextKappa B y)))
        (by rw [← hm]; linarith) (Or.inl (by
          rw [ltop_map_absB, ← hm]
          have h1 : δ + (c - 1) * max δ (max B.sup t) ≤ c * max δ (max B.sup t) := by
            nlinarith [le_max_left δ (max B.sup t)]
          have h2 : (c - 1) * m ≤ (c - 1) * max δ (max B.sup t) :=
            mul_le_mul_of_nonneg_left hmM (by linarith)
          linarith))
        (by rw [hl']; exact hδopt)
        (by rw [hl']; exact le_trans hy hδy)
        (by rw [← hm, hl']; linarith)
      simpa [absL, absB, List.map_append] using this
    · refine ⟨hokP, fun C hC => hnn C (by simp [hC]), ?_, hBnn.2.2, ?_⟩
      · have : 0 ≤ p'' := le_trans (mul_nonneg hc0 hM0) hp
        linarith
      · simp only [optAdd]
        apply le_trans hX
        simp only [gCre]
        cases hκ : B.κ with
        | none =>
          simp only [nextKappa, hκ]
          apply max_le
          · apply le_trans _ (le_max_right _ _); linarith
          · exact le_max_left _ _
        | some k =>
          simp only [nextKappa, hκ]
          apply max_le
          · apply le_trans _ (le_max_right _ _)
            linarith [le_max_right (k + max 0 (y + B.σ - B.p)) y]
          · apply max_le (le_max_left _ _)
            apply le_trans _ (le_max_right _ _)
            have : k + (B.x + B.σ - B.p) ≤ B.x - y + (k + max 0 (y + B.σ - B.p)) := by
              linarith [le_max_right 0 (y + B.σ - B.p)]
            linarith [le_max_left (k + max 0 (y + B.σ - B.p)) y]
  | top B t e D D' he hD =>
    have hBnn := hnn B (by simp)
    have hc0 : (0 : ℝ) ≤ c := by linarith
    simp only [okChain] at hok
    obtain ⟨hx0, heu0, hκ0, -⟩ := hok
    have hM0 : 0 ≤ max B.sup t := le_trans hBnn.1 (le_max_left _ _)
    have he0 : 0 ≤ e := le_trans (mul_nonneg hc0 hM0) he
    refine ⟨?_, ?_⟩
    · have hopt0 : optMax B.eu B.κ = 0 := by rw [heu0, hκ0]; rfl
      have hmx : max (max B.sup t) (optMax B.eu B.κ) = max B.sup t := by
        rw [hopt0]; exact max_eq_left hM0
      have := LStepX.slow (c := c) (β := 1) [] B.sup B.x (optMax B.eu B.κ) t (optMax D.eu D.κ) e
        (optMax D'.eu D'.κ) (by rw [hmx]; exact he)
        (Or.inl (by rw [hmx]; simp [ltop, lsup]; nlinarith))
        (by rw [hopt0]; exact le_trans hD (le_optMax D'.eu D'.κ))
        (le_trans hD (le_optMax D'.eu D'.κ))
        (by rw [hmx, hx0]; linarith [le_trans hD (le_optMax D'.eu D'.κ)])
      simpa [absL, absB] using this
    · exact ⟨by simp [okChain], by simp, he0, hD,
        by simp only [ctop]; exact le_trans hD (le_optAdd D'.eu D'.κ _)⟩

theorem locs_refutation_embeds {c : ℝ} (hc : 1 ≤ c) {n : ℕ} {L : ℕ → CLine}
    (h : LocsRefutes c n L) : LRefutesX c 1 n (fun i => absL (L i)) := by
  obtain ⟨hn, h0, hD0, hκ0, hN, ha, hlt, hstep, hmid⟩ := h
  have hinv : ∀ i, i ≤ n → CInv (L i) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨by rw [h0]; trivial, by rw [h0]; simp, ha, by rw [hD0], ?_⟩
      rw [h0]; simp only [ctop]; rw [hD0]; exact le_optAdd 0 (L 0).2.2.κ _
    | succ i ih => intro hi; exact (locs_embed hc (ih (by omega)) (hstep i (by omega))).2
  refine ⟨hn, by simp [absL, h0], by simp [absL, hN], ha, ?_, hlt, ?_, ?_⟩
  · show 0 ≤ optMax (L 0).2.2.eu (L 0).2.2.κ
    rw [hD0, hκ0]; exact le_rfl
  · intro i hi; exact (locs_embed hc (hinv i hi.le) (hstep i hi)).1
  · intro i h1 h2; simpa [absL] using hmid i h1 h2

/-- Concrete R1L/R1T/C1L derivations (with R0′ and the top-level R2) cannot refute
SAT ∈ DTS(n^c) for c ≥ 2cos(π/7). -/
theorem no_locs_refutation {c : ℝ} (hc : r7 ≤ c) (n : ℕ) (L : ℕ → CLine) : ¬ LocsRefutes c n L := by
  intro h
  have hc1 : (1 : ℝ) ≤ c := le_trans (by linarith [nine_fifths_lt_r7]) hc
  have hcub : (1 - 1) * (c - 1) ^ 2 ≤ cub c := by
    have := (cub_nonneg_iff hc1).mpr hc; simpa using this
  exact no_refutation_locX (by norm_num) le_rfl hc1 hcub n _ (locs_refutation_embeds hc1 h)

/-- The Lipton–Viglas refutation in the concrete model (non-vacuity): R0′, R1L with x = 1/2,
C1L with y = x (here equal to R2), top-level R2, at c = 7/5. The initial `κ = none` encodes
"no arrays", so the first index block has superscript 0, as in R1L. -/
noncomputable def lvC : ℕ → CLine
  | 0 => ([], 1, ⟨0, none, 0⟩)
  | 1 => ([⟨0, 0, 0, 0, none, 0⟩], 1, ⟨0, none, 0⟩)
  | 2 => ([⟨max 0 (1/2), 0, 0, 0, none, 0⟩, ⟨0, 1/2, 1 - 1/2, 0, none, 0⟩],
      1 - 1/2, ⟨0, none, 0⟩)
  | 3 => ([⟨max 0 (1/2), 0, 0, 0, none, 0⟩], 1/2 - 1/2 + 7/10,
      ⟨7/10, some (1/2), 0⟩)
  | _ => ([], 49/50, ⟨0, none, 0⟩)

theorem lv_locs_refutes : LocsRefutes (7/5) 4 lvC := by
  refine ⟨by norm_num, rfl, rfl, rfl, rfl, by norm_num [lvC], by norm_num [lvC], ?_, ?_⟩
  · intro i hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    · exact LocsStep.init 1 ⟨0, none, 0⟩
    · exact LocsStep.r1l [] ⟨0, 0, 0, 0, none, 0⟩ 1 ⟨0, none, 0⟩ (1/2) 0 (by norm_num)
        (by norm_num) (by norm_num)
    · exact LocsStep.c1l (c := 7/5) [⟨max 0 (1/2), 0, 0, 0, none, 0⟩]
        ⟨0, 1/2, 1 - 1/2, 0, none, 0⟩ (1 - 1/2) ⟨0, none, 0⟩ (1/2) (7/10)
        (by simp) (by norm_num) (by norm_num) (by simp only [cDelta, optAdd]; norm_num [max_def])
    · exact LocsStep.top ⟨max 0 (1/2), 0, 0, 0, none, 0⟩ (1/2 - 1/2 + 7/10) (49/50) _ ⟨0, none, 0⟩
        (by norm_num [max_def]) le_rfl
  · intro i h1 h2
    obtain rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals simp [lvC]

end PastaMath.SatBarriers
