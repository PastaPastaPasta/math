-- SPDX-License-Identifier: Apache-2.0
import PastaMath.TwoCutSoS

/-! Audit for the headline theorems of `PastaMath.TwoCutSoS`. -/

open PastaMath.TwoCutSoS

-- Exact dictionary (Defs, Dictionary)
#print axioms hasPTRank_iff_hasTwoCut
#print axioms prod_of_twoCut
#print axioms twoCut_of_sos
#print axioms twoCut_of_prod
#print axioms sos_of_prod
#print axioms sos_of_twoCut
#print axioms sos_of_ptRank
#print axioms crossing_prod_of_twoCut
#print axioms crossing_twoCut_of_sos
#print axioms crossing_twoCut_of_prod
#print axioms crossing_sos_of_twoCut

-- Rossman–Zhu §3.2 counterexamples (RossmanZhu)
#print axioms rz_lemma313_counterexample
#print axioms rzM1_hasSoS_two
#print axioms rz_prop316_left_counterexample
#print axioms rzM2_hasSoS_four
#print axioms rz_prop316_right_counterexample

-- Characteristic-free crossing bounds & exact values (LowerBounds)
#print axioms twoCut_ge_max
#print axioms twoCut_gt_max_of_ge_three
#print axioms twoCut_two_iff
#print axioms transpose_twoCut
#print axioms twoCut_three_three_iff

-- Explicit constructions & border decompositions (Witnesses)
#print axioms clifford_twoCut
#print axioms exact_of_border_coeffs
#print axioms tc45_twoCut
#print axioms tc46_twoCut
#print axioms tc88_twoCut
#print axioms border44_identity_field

-- Reflection-type word-span tensor powers (ReflectionPowers)
#print axioms reflOp_involutive
#print axioms reflOp_selfadjoint
#print axioms wordPoly_eval_B
#print axioms reflection_slice_constraint
#print axioms valuation_theorem
#print axioms layer_grouping_le
#print axioms CertPacking.lower_bound
#print axioms CertPacking.asymptotic_bound
#print axioms packing_K4_quarter_value
#print axioms reflection_wordSpan_nogo
