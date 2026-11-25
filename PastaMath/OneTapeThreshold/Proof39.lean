-- SPDX-License-Identifier: Apache-2.0
import PastaMath.OneTapeThreshold.Calculus
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Williams's quintic p_d and a 39-line proof above r₁

`pd d x` is the polynomial p_d(x) of Williams's Theorem 7.5 (TOCT p. A:33), whose root r_d ≥ 1 is
the exponent of that theorem. `pd1_root_lt`, `pd2_root_lt`, `pd3_root_lt`: every real root of p_d
is below 1.301, 1.1888 and 1.1373 for d = 1, 2, 3 (p_d is positive from there on: after the shift
x = ρ + t every coefficient is positive). `pd1_neg_lo`, `pd2_neg_lo`, `pd3_neg_lo`: p_d is negative
at 1.3009, 1.1887 and 1.1372.

`cert39` is a 38-step tag list at c = 26019/20000 = 1.30095, d = 1, from a₀ = 10⁵, with rule word
11101101101100111011011001101101101100 (1 = speedup: Lemma 7.1 on a DTIME_d kernel or Lemma 3.3
on a DTISP kernel; 0 = Lemma 7.2). `cert39_ok` checks it with `nfCheck` and `cert39_time` checks that
every line it produces has kernel time ≥ input superscript (`timeCheck`); both by `decide +kernel`.
`cert39_above_r1`: a strict normal-form proof exists at c = 1.30095 and every real root of p₁ is
below 1.30095. `cert39_spec` states the 39-line proof in one theorem: `NF (26019/20000) 1 M 38` with
`M 0 = ([], T 100000)` and kernel time ≥ input superscript on every line `M i`, i ≤ 38, and the
root bound.
-/

namespace PastaMath.OneTapeThreshold
namespace HY

set_option maxRecDepth 100000

/-- Williams's polynomial of Theorem 7.5:
p_d(x) = (2d+1)(d+1)²x⁵ − 2(d+1)(2d+1)x⁴ − d²x³ + 2(d+1)x² − ((2d+1)(d+1)²+1)x + d(d+1). -/
def pd (d x : ℝ) : ℝ := (2*d+1)*(d+1)^2*x^5 - 2*(d+1)*(2*d+1)*x^4 - d^2*x^3 + 2*(d+1)*x^2 -
  ((2*d+1)*(d+1)^2+1)*x + d*(d+1)

/-- p₁(x) > 0 for every real x ≥ 1301/1000. -/
theorem pd1_pos (x : ℝ) (hx : (1301 / 1000 : ℝ) ≤ x) : 0 < pd 1 x := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ x = (1301 / 1000 : ℝ) + t := ⟨x - (1301 / 1000 : ℝ), by linarith, by ring⟩
  have h : pd 1 ((1301 / 1000 : ℝ) + t) = (835549866503 / 250000000000000 : ℝ) * t ^ 0 + (2926226923203 / 50000000000 : ℝ) * t ^ 1 + (3561964903 / 25000000 : ℝ) * t ^ 2 + (3491603 / 25000 : ℝ) * t ^ 3 + (3303 / 50 : ℝ) * t ^ 4 + (12 : ℝ) * t ^ 5 := by unfold pd; ring
  rw [h]; positivity

/-- p₁(13009/10000) < 0. -/
theorem pd1_neg_lo : pd 1 (13009 / 10000 : ℝ) < 0 := by unfold pd; norm_num

/-- Every real root of p₁ is below 1301/1000. -/
theorem pd1_root_lt {x : ℝ} (h : pd 1 x = 0) : x < (1301 / 1000 : ℝ) := by
  by_contra hc; have := pd1_pos x (not_lt.mp hc); linarith

/-- p₂(x) > 0 for every real x ≥ 743/625 = 1.1888. -/
theorem pd2_pos (x : ℝ) (hx : (743 / 625 : ℝ) ≤ x) : 0 < pd 2 x := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ x = (743 / 625 : ℝ) + t := ⟨x - (743 / 625 : ℝ), by linarith, by ring⟩
  have h : pd 2 ((743 / 625 : ℝ) + t) = (39896097487 / 19073486328125 : ℝ) * t ^ 0 + (1215105070859 / 6103515625 : ℝ) * t ^ 1 + (4818164076 / 9765625 : ℝ) * t ^ 2 + (7645382 / 15625 : ℝ) * t ^ 3 + (5937 / 25 : ℝ) * t ^ 4 + (45 : ℝ) * t ^ 5 := by unfold pd; ring
  rw [h]; positivity

/-- p₂(11887/10000) < 0. -/
theorem pd2_neg_lo : pd 2 (11887 / 10000 : ℝ) < 0 := by unfold pd; norm_num

/-- Every real root of p₂ is below 743/625 = 1.1888. -/
theorem pd2_root_lt {x : ℝ} (h : pd 2 x = 0) : x < (743 / 625 : ℝ) := by
  by_contra hc; have := pd2_pos x (not_lt.mp hc); linarith

/-- p₃(x) > 0 for every real x ≥ 11373/10000. -/
theorem pd3_pos (x : ℝ) (hx : (11373 / 10000 : ℝ) ≤ x) : 0 < pd 3 x := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ x = (11373 / 10000 : ℝ) + t := ⟨x - (11373 / 10000 : ℝ), by linarith, by ring⟩
  have h : pd 3 ((11373 / 10000 : ℝ) + t) = (57593092563231651 / 6250000000000000000 : ℝ) * t ^ 0 + (59706158409160487 / 125000000000000 : ℝ) * t ^ 1 + (7439127980819 / 6250000000 : ℝ) * t ^ 2 + (740568903 / 625000 : ℝ) * t ^ 3 + (72611 / 125 : ℝ) * t ^ 4 + (112 : ℝ) * t ^ 5 := by unfold pd; ring
  rw [h]; positivity

/-- p₃(2843/2500) < 0 (2843/2500 = 1.1372). -/
theorem pd3_neg_lo : pd 3 (2843 / 2500 : ℝ) < 0 := by unfold pd; norm_num

/-- Every real root of p₃ is below 11373/10000. -/
theorem pd3_root_lt {x : ℝ} (h : pd 3 x = 0) : x < (11373 / 10000 : ℝ) := by
  by_contra hc; have := pd3_pos x (not_lt.mp hc); linarith

/-- Accepts when the tags replay from `([], T a0)` and every line produced has kernel time ≥ its
input superscript (`pinQ`). -/
def timeCheck (c d a0 : ℚ) (ts : List Tag) : Bool :=
  match runQ c d ([], .T a0) ts with
  | none => false
  | some ls => ls.all (fun L => decide (pinQ L.1 ≤ L.2.time))

/-- The 38 tags of a 39-line proof at c = 26019/20000, d = 1, from a₀ = 10⁵; rule word
11101101101100111011011001101101101100 (1 = Lemma 7.1 or Lemma 3.3, 0 = Lemma 7.2). -/
def cert39 : List Tag :=
  [.convNew true (8709140938476740848273 / 200000000000000000 : ℚ),
    .speedMerge (12908590615232591517269 / 1000000000000000000 : ℚ),
    .speedMerge (14920372292792249936611 / 1000000000000000000 : ℚ),
    .slow,
    .convMerge (17712416859814589632151 / 500000000000000000 : ℚ),
    .speedMerge (5760310816386675400281 / 250000000000000000 : ℚ),
    .slow,
    .convMerge (33705797869927287397877 / 1000000000000000000 : ℚ),
    .speedMerge (3095034889406077273361 / 125000000000000000 : ℚ),
    .slow,
    .convMerge (14616519246293951396001 / 500000000000000000 : ℚ),
    .speedMerge (29233038492587851860299 / 1000000000000000000 : ℚ),
    .slow,
    .slow,
    .convMerge (21248919386559465265131 / 500000000000000000 : ℚ),
    .speedMerge (8291951750149631179633 / 500000000000000000 : ℚ),
    .speedMerge (6978228267248719930649 / 500000000000000000 : ℚ),
    .slow,
    .convMerge (32546002137447441679979 / 1000000000000000000 : ℚ),
    .speedMerge (23908293170168839321559 / 1000000000000000000 : ℚ),
    .slow,
    .convMerge (28227147653808217567349 / 1000000000000000000 : ℚ),
    .speedMerge (7056786913452032095627 / 250000000000000000 : ℚ),
    .slow,
    .slow,
    .convMerge (36465509855864971724573 / 1000000000000000000 : ℚ),
    .speedMerge (4523246483510660291603 / 200000000000000000 : ℚ),
    .slow,
    .convMerge (17898933910278360546363 / 500000000000000000 : ℚ),
    .speedMerge (23283874452861304128601 / 1000000000000000000 : ℚ),
    .slow,
    .convMerge (34060730008888506358927 / 1000000000000000000 : ℚ),
    .speedMerge (2502101226452949465529 / 100000000000000000 : ℚ),
    .slow,
    .convMerge (14770435568354504967647 / 500000000000000000 : ℚ),
    .speedMerge (29540871136708758548511 / 1000000000000000000 : ℚ),
    .slow,
    .slow]

/-- `cert39` passes `nfCheck` at c = 26019/20000, d = 1, a₀ = 100000. -/
theorem cert39_ok : nfCheck (26019 / 20000 : ℚ) 1 100000 cert39 = true := by decide +kernel
/-- Every line produced by `cert39` from `([], T 100000)` has kernel time ≥ input superscript. -/
theorem cert39_time : timeCheck (26019 / 20000 : ℚ) 1 100000 cert39 = true := by decide +kernel
/-- A strict normal-form proof exists at c = 26019/20000 = 1.30095, d = 1. -/
theorem cert39_nf : ∃ M n, NF (26019 / 20000 : ℝ) 1 M n := by
  have h := nfCheck_sound cert39_ok; push_cast at h; exact h

/-- p₁(x) > 0 for every real x ≥ 26019/20000. -/
theorem pd1_pos' (x : ℝ) (hx : (26019 / 20000 : ℝ) ≤ x) : 0 < pd 1 x := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ x = (26019 / 20000 : ℝ) + t := ⟨x - (26019 / 20000 : ℝ), by linarith, by ring⟩
  have h : pd 1 ((26019 / 20000 : ℝ) + t) = (333062977473358297 / 800000000000000000000 : ℝ) * t ^ 0 + (468082333215166963 / 8000000000000000 : ℝ) * t ^ 1 + (28491529498577 / 200000000000 : ℝ) * t ^ 2 + (1396509083 / 10000000 : ℝ) * t ^ 3 + (66057 / 1000 : ℝ) * t ^ 4 + (12 : ℝ) * t ^ 5 := by unfold pd; ring
  rw [h]; positivity

/-- A strict normal-form proof exists at c = 26019/20000, d = 1, and every real root of p₁ is
below 26019/20000. -/
theorem cert39_above_r1 : (∃ M n, NF (26019 / 20000 : ℝ) 1 M n) ∧ ∀ x, pd 1 x = 0 → x < 26019 / 20000 :=
  ⟨cert39_nf, fun x h => by
    by_contra hc; push Not at hc; have := pd1_pos' x hc; linarith⟩

/-- The 39-line proof as a single statement: there is a strict normal-form proof `NF c 1 M 38` at
c = 26019/20000 (lines `M 0, …, M 38`, each obtained from the previous one by a `Step`) with
`M 0 = ([], T 100000)`, kernel time ≥ input superscript on every line `M i`, i ≤ 38, and every real
root of p₁ is below c. -/
theorem cert39_spec :
    (∃ M : ℕ → Line, NF (26019 / 20000 : ℝ) 1 M 38 ∧ M 0 = ([], .T 100000) ∧
      ∀ i ≤ 38, pin (M i).1 ≤ (M i).2.time) ∧
    ∀ x, pd 1 x = 0 → x < 26019 / 20000 := by
  refine ⟨?_, cert39_above_r1.2⟩
  obtain ⟨ls, hr, hnf⟩ := nfCheck_spec cert39_ok
  have ht := cert39_time
  simp only [timeCheck, hr, List.all_eq_true, decide_eq_true_eq] at ht
  have hlen : cert39.length = 38 := by decide
  obtain ⟨hl, hhead, -⟩ := runQ_spec cert39 _ ls hr
  have hls : ls.length = 39 := by rw [hl, hlen]
  have h0 : ls.getD 0 ([], .T 100000) = ([], .T 100000) := by
    cases ls with
    | nil => simp at hls
    | cons L rest => simpa using hhead
  rw [hlen] at hnf
  push_cast at hnf
  refine ⟨_, hnf, by show castL _ = _; rw [h0]; simp [castL, castK], fun i hi => ?_⟩
  have hi' : i < ls.length := by omega
  have hmem := ht _ (List.getElem_mem hi')
  rw [getD_lt hi']
  simp only [castL, pin_cast, time_cast]
  exact_mod_cast hmem

end HY
end PastaMath.OneTapeThreshold
