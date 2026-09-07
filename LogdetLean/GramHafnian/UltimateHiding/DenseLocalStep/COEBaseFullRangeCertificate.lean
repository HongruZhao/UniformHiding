import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.COEBaseDenseCertificate
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteFullRangeCertificate
import LogdetLean.GramHafnian.UltimateHiding.SquaredCompletionRawDensity
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19QuantitativeEndpoint

/-!
# Full-range squared hiding from a canonical square-COE score certificate

This is the paper-facing composition for the reduced score interface.  The
dense score calculation is required only at the canonical scaled-COE square
base.  Radial propagation supplies every rectangular dense ambient law, and
the finite Jiang branch supplies the complementary `K < 16N` range.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

/-- Full-range squared matrix hiding from the canonical square-COE score
certificate.  In the active raw-density proof, the displayed reserve `106`
dominates both the dense reserve `72` and the elementary sparse coefficient
`68`.  The conclusion covers every finite `1 <= N <= K <= M`, including
`K=M`. -/
theorem uniformProductMatrixHidingSquaredAt_of_canonicalCOEBaseScoreCertificate
    {CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ}
    (hscore : UniformCanonicalScaledCOESharedBetaScoreCertificateAt
      CscoreOne CscoreTwo CorbitalTwo CorbitalThree) :
    UniformProductMatrixHidingSquaredAt
      (4 * CscoreOne + 5 * CscoreTwo +
        2 * CorbitalTwo + 2 * CorbitalThree + 106) := by
  let Cdense : ℝ :=
    4 * CscoreOne + 5 * CscoreTwo +
      2 * CorbitalTwo + 2 * CorbitalThree + 72
  let Cglobal : ℝ :=
    4 * CscoreOne + 5 * CscoreTwo +
      2 * CorbitalTwo + 2 * CorbitalThree + 106
  have hlocalDense : Dense.ConcreteDenseSquaredLocalStepAt Cdense 24 16 :=
    concreteDenseSquaredLocalStepAt_of_canonicalCOEBaseScoreCertificate hscore
  have hCdense : 0 ≤ Cdense := hlocalDense.constant_nonneg
  have hCdenseGlobal : Cdense ≤ Cglobal := by
    dsimp [Cdense, Cglobal]
    linarith
  have hlocalGlobal :
      Dense.ConcreteDenseSquaredLocalStepAt Cglobal 24 16 :=
    concreteDenseSquaredLocalStepAt_mono hCdenseGlobal hlocalDense
  have hCglobal : 1 ≤ Cglobal := by
    dsimp [Cdense, Cglobal] at hCdense ⊢
    linarith
  have hC0global : (24 : ℝ) ≤ Cglobal := by
    dsimp [Cdense, Cglobal] at hCdense ⊢
    linarith
  have hsample := hscore 1 16 24
    (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  have hsparseGlobal :
      Sparse.rawDensitySparseSquaredCoefficient 16 ≤ Cglobal := by
    rw [Sparse.rawDensitySparseSquaredCoefficient_sixteen]
    have h1 := hsample.scoreOne_nonneg
    have h2 := hsample.scoreTwo_nonneg
    have h3 := hsample.orbitalTwo_nonneg
    have h4 := hsample.orbitalThree_nonneg
    dsimp [Cglobal]
    nlinarith
  exact
    uniformProductMatrixHidingSquaredAt_of_denseLocalStep_of_rawDensityQuantitative
      Sparse.rawDensityTransposeGramQuantitative_proved
      hCglobal hC0global (by norm_num : 16 + 1 ≤ 24)
      hsparseGlobal hlocalGlobal

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
