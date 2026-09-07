import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteDenseCertificate
import LogdetLean.GramHafnian.UltimateHiding.SquaredCompletionRawDensity
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19QuantitativeEndpoint

/-!
# Full-range squared hiding from the concrete score certificate

This file performs only interface composition.  The dense same-beta score
certificate remains an explicit theorem argument.  The dense one-step bound
uses cutoff `K >= 16 N` and ambient threshold `m >= 24 N^2`; the complementary
bounded-aspect branch is proved directly from Jiang's raw Haar-corner density.
Its elementary squared-rate conversion has coefficient `68` at `kappa = 16`;
the displayed paper constant `106` already dominates this coefficient.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LocalAnticoncentration

/-- A dense local-step certificate remains valid when its numerical
coefficient is enlarged. -/
theorem concreteDenseSquaredLocalStepAt_mono
    {C D : ℝ} {C0 kappa : ℕ} (hCD : C ≤ D)
    (hlocal : Dense.ConcreteDenseSquaredLocalStepAt C C0 kappa) :
    Dense.ConcreteDenseSquaredLocalStepAt D C0 kappa := by
  refine ⟨hlocal.constant_nonneg.trans hCD, ?_⟩
  intro H N K m hN hNK hKm hlarge hdense
  exact (hlocal.apply H hN hNK hKm hlarge hdense).mono (by
    unfold Dense.denseTelescopingRate
    gcongr)

/-- Paper-facing all-range theorem conditional only on the explicit uniform
same-beta score certificate.  The coefficient `106` supplies the dense
budget's fixed `72` and also dominates the raw-density sparse coefficient
`68`; the four displayed score contributions are unchanged.

Consequently the conclusion covers every finite `1 <= N <= K <= M`, including
both the square endpoint `K=M` and all rectangular cases. -/
theorem uniformProductMatrixHidingSquaredAt_of_uniformScoreCertificate
    {CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ}
    (hscore : UniformConcreteSharedBetaScoreCertificateAt
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
  have hlocalDense : Dense.ConcreteDenseSquaredLocalStepAt Cdense 24 16 := by
    exact concreteDenseSquaredLocalStepAt_of_uniformScoreCertificate hscore
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
  have hsample := hscore
    canonicalUnitaryHaarProbabilityFamily 1 16 24
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
  have hglobal :=
    uniformProductMatrixHidingSquaredAt_of_denseLocalStep_of_rawDensityQuantitative
      Sparse.rawDensityTransposeGramQuantitative_proved
      hCglobal hC0global (by norm_num : 16 + 1 ≤ 24)
      hsparseGlobal hlocalGlobal
  exact hglobal

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
