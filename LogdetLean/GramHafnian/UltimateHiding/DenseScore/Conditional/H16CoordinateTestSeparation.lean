import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16TestPairToBochner

/-!
# Concrete coordinate test separation for H16

This module discharges the purely foundational finite-dimensional separation
premise isolated by `H16TestPairToBochner`.  It contains no scientific axiom,
determinant estimate, event derivative, or H5 input.
-/

open MeasureTheory
open scoped ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 2000000 in
/-- Compactly supported smooth tests separate the concrete independent
complex-symmetric-coordinate `L1` space. -/
theorem h16CenteredCoordinateTestPairingSeparates_proved (N : ℕ) :
    H16CenteredCoordinateTestPairingSeparates N := by
  intro f g hpair
  apply Conditional.h16_l1_eq_of_integral_test_mul_eq f g
  intro phi hphi hsupp
  rw [← Conditional.h16TestPairCLM_apply phi hphi hsupp f]
  rw [← Conditional.h16TestPairCLM_apply phi hphi hsupp g]
  exact hpair phi hphi hsupp

/-- The scalar compact-test interval family therefore gives the exact four
scientific inputs consumed by U07, with no additional foundational premise. -/
theorem h16DownstreamCompactL1ScientificInputs_of_testPair_exactH5_provedSeparation
    (hH5 : H16ExactH5Family) (W : H16CenteredWeakFactsFamily)
    (T : H16CenteredShiftedTestPairIntervalFamily W) :
    H16DownstreamCompactL1ScientificInputs :=
  h16DownstreamCompactL1ScientificInputs_of_testPair_exactH5
    h16CenteredCoordinateTestPairingSeparates_proved hH5 W T

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
