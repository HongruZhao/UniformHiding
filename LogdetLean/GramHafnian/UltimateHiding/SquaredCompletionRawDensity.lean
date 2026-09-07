import LogdetLean.GramHafnian.UltimateHiding.Dense.SquaredEndpoint
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19RawBranchBridge

/-!
# Squared-rate completion from the quantitative raw-density theorem

This module assembles the all-rank squared hiding theorem from two explicit
premises: the concrete dense local step and the quantitative rectangular
total-variation statement targeted by the raw Jiang-density proof.  The
legacy sparse likelihood and Jacobi-factorization endpoint is not imported.
-/

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open MeasureTheory
open CurrentPRL

/-- The universal finite raw-density estimate tends to zero along every fixed
rectangular block.  This is the target-convergence input for the generic
dense telescope, derived without calling the source-specific Jiang endpoint. -/
theorem Dense.rawDensity_denseHaarAmbient_targetConvergence_unrestricted
    (hraw : Sparse.RawDensityTransposeGramQuantitative)
    (H : UnitaryHaarProbabilityFamily) {N K start : Nat}
    (hN : 0 < N) (hK : 0 < K) (hNK : N <= K) :
    forall epsilon : Real, 0 < epsilon ->
      exists n : Nat,
        Dense.ProbabilityTVLE
          (Dense.denseHaarAmbientLaw H N K (start + n))
          (Dense.denseGaussianTransposeGramTarget N K) epsilon := by
  intro epsilon hepsilon
  let c : Real :=
    ((K : Real) + N) * Real.sqrt ((K : Real) * N)
  have hc : 0 <= c := by
    dsimp [c]
    positivity
  obtain ⟨q, hq⟩ := Dense.exists_nat_fixed_div_add_le
    c epsilon (start + (K + N + 1)) hc hepsilon
  refine ⟨K + N + 1 + q, ?_⟩
  have hstrict : K + N < start + (K + N + 1 + q) := by omega
  have hrawBound := hraw H (start + (K + N + 1 + q)) N K
    hN hK hNK hstrict
  apply hrawBound.mono
  change c / ((start + (K + N + 1 + q) : Nat) : Real) <= epsilon
  have hden :
      start + (K + N + 1 + q) = (start + (K + N + 1)) + q := by
    omega
  rw [hden]
  exact hq

/-- Dense very-large branch using `hraw` itself for target convergence.
Keeping this adapter local prevents the source-specific target theorem in
`Dense.SquaredEndpoint` from entering the composition's dependency closure. -/
private theorem veryLargeDenseSquaredBranchAt_of_localStep_of_rawDensityQuantitative
    {C : Real} {C0 kappa : Nat}
    (hraw : Sparse.RawDensityTransposeGramQuantitative)
    (hlocal : Dense.ConcreteDenseSquaredLocalStepAt C C0 kappa) :
    VeryLargeDenseSquaredBranchAt C C0 kappa := by
  intro H M N K hN hNK hKM hlarge hdense
  have hNpos : 0 < N := by omega
  have hKpos : 0 < K := hNpos.trans_le hNK
  have hMpos : 1 <= M := by omega
  have hstep : forall m, M <= m ->
      Dense.ProbabilityTVLE
        (Dense.denseHaarAmbientLaw H N K m)
        (Dense.denseHaarAmbientLaw H N K (m + 1))
        (Dense.denseTelescopingRate C N m) := by
    intro m hMm
    exact hlocal.apply H hN hNK (hKM.trans hMm)
      (hlarge.trans hMm) hdense
  have hglobal := Dense.probabilityTVLE_dense_telescope_from
    (Dense.denseHaarAmbientLaw H N K)
    (Dense.denseGaussianTransposeGramTarget N K)
    C N M hlocal.constant_nonneg hMpos hstep
    (Dense.rawDensity_denseHaarAmbient_targetConvergence_unrestricted
      hraw H hNpos hKpos hNK)
  letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
    scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
  letI : IsProbabilityMeasure (gaussianTransposeGramLaw N K) :=
    gaussianTransposeGramLaw_isProbability N K
  have hcap := probabilityTotalVariationLE_min_one hglobal
  simpa only [ultimateSquaredHidingRate, mul_div_assoc] using hcap

/-- Paper-facing all-rank squared theorem from the literal dense local step
and the explicit quantitative raw-density statement. -/
theorem uniformProductMatrixHidingSquaredAt_of_denseLocalStep_of_rawDensityQuantitative
    {C : Real} {C0 kappa : Nat}
    (hraw : Sparse.RawDensityTransposeGramQuantitative)
    (hC : 1 <= C) (hC0 : (C0 : Real) <= C)
    (hkappaC0 : kappa + 1 <= C0)
    (hsparseC : Sparse.rawDensitySparseSquaredCoefficient kappa <= C)
    (hlocal : Dense.ConcreteDenseSquaredLocalStepAt C C0 kappa) :
    UniformProductMatrixHidingSquaredAt C := by
  exact uniformProductMatrixHidingSquaredAt_of_largeAmbientBranches
    hC kappa
    (LargeAmbientDenseSquaredBranchAt.of_veryLarge hC0
      (veryLargeDenseSquaredBranchAt_of_localStep_of_rawDensityQuantitative
        hraw hlocal))
    (Sparse.largeAmbientSparseSquaredBranchAt_of_rawDensityQuantitative
      hraw hC0 hkappaC0 hsparseC)

/-- Existential all-rank squared theorem with the same two explicit premises. -/
theorem uniformProductMatrixHidingSquared_of_denseLocalStep_of_rawDensityQuantitative
    {C : Real} {C0 kappa : Nat}
    (hraw : Sparse.RawDensityTransposeGramQuantitative)
    (hC : 1 <= C) (hC0 : (C0 : Real) <= C)
    (hkappaC0 : kappa + 1 <= C0)
    (hsparseC : Sparse.rawDensitySparseSquaredCoefficient kappa <= C)
    (hlocal : Dense.ConcreteDenseSquaredLocalStepAt C C0 kappa) :
    UniformProductMatrixHidingSquared :=
  ⟨C,
    uniformProductMatrixHidingSquaredAt_of_denseLocalStep_of_rawDensityQuantitative
      hraw hC hC0 hkappaC0 hsparseC hlocal⟩

end

end LogdetLean.GramHafnian.UltimateHiding
