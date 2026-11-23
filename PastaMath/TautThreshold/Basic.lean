-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
List helpers shared by the TAUT-threshold files. `top l` is the last entry of `l`
(the innermost input constraint when `l` lists constraints outermost first), and `0` for `[]`.
-/

namespace PastaMath.TautThreshold

def top (l : List ℝ) : ℝ := l.getD (l.length - 1) 0

theorem top_concat (bs : List ℝ) (b : ℝ) : top (bs ++ [b]) = b := by
  unfold top
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

theorem top_eq_getD {l : List ℝ} {k : ℕ} (h : l.length = k + 1) : top l = l.getD k 0 := by
  unfold top
  rw [h, Nat.add_sub_cancel]

end PastaMath.TautThreshold
