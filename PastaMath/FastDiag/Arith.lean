-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace PastaMath.FastDiag

open Real

theorem log_saving_linear {A K n V : ℝ} (hA : 0 ≤ A) (hn : 2 ≤ n) (hVn : n ≤ V)
    (hV : V ≤ K * n * logb 2 n) : A * V / logb 2 V ≤ A * K * n := by
  have hL : 0 < logb 2 n := logb_pos one_lt_two (by linarith)
  have hLV : logb 2 n ≤ logb 2 V := logb_le_logb_of_le one_lt_two (by linarith) hVn
  have h1 : A * V / logb 2 V ≤ A * V / logb 2 n :=
    div_le_div_of_nonneg_left (mul_nonneg hA (by linarith)) hL hLV
  have h2 : A * V / logb 2 n ≤ A * (K * n * logb 2 n) / logb 2 n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hV hA) hL.le
  have h3 : A * (K * n * logb 2 n) / logb 2 n = A * K * n := by
    field_simp
  linarith

theorem sqrt_saving_linear {A K n V : ℝ} (hA : 0 ≤ A) (hn : 2 ≤ n) (hVn : n ≤ V)
    (hV : V ≤ K * n * √(logb 2 n)) : A * V / √(logb 2 V) ≤ A * K * n := by
  have hL : 0 < √(logb 2 n) := Real.sqrt_pos.mpr (logb_pos one_lt_two (by linarith))
  have hLV : √(logb 2 n) ≤ √(logb 2 V) :=
    Real.sqrt_le_sqrt (logb_le_logb_of_le one_lt_two (by linarith) hVn)
  have h1 : A * V / √(logb 2 V) ≤ A * V / √(logb 2 n) :=
    div_le_div_of_nonneg_left (mul_nonneg hA (by linarith)) hL hLV
  have h2 : A * V / √(logb 2 n) ≤ A * (K * n * √(logb 2 n)) / √(logb 2 n) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hV hA) hL.le
  have h3 : A * (K * n * √(logb 2 n)) / √(logb 2 n) = A * K * n := by
    field_simp
  linarith

theorem sqrt_saving_superlinear {A K n V : ℝ} (hA : 0 < A) (hK : 0 < K) (hn : 2 ≤ n)
    (hVn : n ≤ V) (hV : K * n * logb 2 n ≤ V) (hV2 : logb 2 V ≤ 2 * logb 2 n) :
    A * K * n * √(logb 2 n) ≤ √2 * (A * V / √(logb 2 V)) := by
  have hL : 0 < logb 2 n := logb_pos one_lt_two (by linarith)
  have hs : 0 < √(logb 2 n) := Real.sqrt_pos.mpr hL
  have hsq : √(logb 2 n) * √(logb 2 n) = logb 2 n := Real.mul_self_sqrt hL.le
  have hVL : 0 < logb 2 V := logb_pos one_lt_two (by linarith)
  have h2pos : 0 < √(2 : ℝ) := by positivity
  have h1 : √(logb 2 V) ≤ √2 * √(logb 2 n) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hV2
  have h2 : A * V / (√2 * √(logb 2 n)) ≤ A * V / √(logb 2 V) :=
    div_le_div_of_nonneg_left (mul_nonneg hA.le (by linarith)) (Real.sqrt_pos.mpr hVL) h1
  have h3 : √2 * (A * V / (√2 * √(logb 2 n))) = A * V / √(logb 2 n) := by
    field_simp
  have h4 : A * (K * n * logb 2 n) / √(logb 2 n) ≤ A * V / √(logb 2 n) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hV hA.le) hs.le
  have h5 : A * (K * n * logb 2 n) / √(logb 2 n) = A * K * n * √(logb 2 n) := by
    calc A * (K * n * logb 2 n) / √(logb 2 n)
        = A * (K * n * (√(logb 2 n) * √(logb 2 n))) / √(logb 2 n) := by rw [hsq]
      _ = A * K * n * √(logb 2 n) := by field_simp
  have h6 : √2 * (A * V / (√2 * √(logb 2 n))) ≤ √2 * (A * V / √(logb 2 V)) :=
    mul_le_mul_of_nonneg_left h2 h2pos.le
  linarith

theorem ew_threshold {A E m V : ℝ} (hA : 0 < A) (hm : 2 ≤ m) (hVm : m ≤ V)
    (hV : V ≤ m * √(logb 2 m) / A - E * m) :
    A * V / √(logb 2 V) ≤ m - A * E * m / √(logb 2 m) := by
  have hs : 0 < √(logb 2 m) := Real.sqrt_pos.mpr (logb_pos one_lt_two (by linarith))
  have hLV : √(logb 2 m) ≤ √(logb 2 V) :=
    Real.sqrt_le_sqrt (logb_le_logb_of_le one_lt_two (by linarith) hVm)
  have h1 : A * V / √(logb 2 V) ≤ A * V / √(logb 2 m) :=
    div_le_div_of_nonneg_left (mul_nonneg hA.le (by linarith)) hs hLV
  have h2 : A * V / √(logb 2 m) ≤ A * (m * √(logb 2 m) / A - E * m) / √(logb 2 m) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hV hA.le) hs.le
  have h3 : A * (m * √(logb 2 m) / A - E * m) / √(logb 2 m)
      = m - A * E * m / √(logb 2 m) := by
    field_simp
  linarith

theorem ew_threshold_sharp {A ε m V : ℝ} (hA : 0 < A) (hε : 0 ≤ ε) (hm : 2 ≤ m)
    (hVm : m ≤ V) (hV : (1 + ε) * m * √(logb 2 m) / A ≤ V)
    (hlog : logb 2 V ≤ (1 + ε) * logb 2 m) :
    √(1 + ε) * m ≤ A * V / √(logb 2 V) := by
  have hL : 0 < logb 2 m := logb_pos one_lt_two (by linarith)
  have hs : 0 < √(logb 2 m) := Real.sqrt_pos.mpr hL
  have ht : 0 < √(1 + ε) := Real.sqrt_pos.mpr (by linarith)
  have htt : √(1 + ε) * √(1 + ε) = 1 + ε := Real.mul_self_sqrt (by linarith)
  have hVL : 0 < logb 2 V := logb_pos one_lt_two (by linarith)
  have h1 : √(logb 2 V) ≤ √(1 + ε) * √(logb 2 m) := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt hlog
  have hAV : (1 + ε) * m * √(logb 2 m) ≤ A * V := by
    have := mul_le_mul_of_nonneg_left hV hA.le
    have hc : A * ((1 + ε) * m * √(logb 2 m) / A) = (1 + ε) * m * √(logb 2 m) := by
      field_simp
    linarith
  have h2 : A * V / (√(1 + ε) * √(logb 2 m)) ≤ A * V / √(logb 2 V) :=
    div_le_div_of_nonneg_left (mul_nonneg hA.le (by linarith)) (Real.sqrt_pos.mpr hVL) h1
  have h3 : (1 + ε) * m * √(logb 2 m) / (√(1 + ε) * √(logb 2 m))
      ≤ A * V / (√(1 + ε) * √(logb 2 m)) :=
    div_le_div_of_nonneg_right hAV (by positivity)
  have h4 : (1 + ε) * m * √(logb 2 m) / (√(1 + ε) * √(logb 2 m)) = √(1 + ε) * m := by
    calc (1 + ε) * m * √(logb 2 m) / (√(1 + ε) * √(logb 2 m))
        = (√(1 + ε) * √(1 + ε)) * m * √(logb 2 m) / (√(1 + ε) * √(logb 2 m)) := by rw [htt]
      _ = √(1 + ε) * m := by field_simp
  linarith

end PastaMath.FastDiag
