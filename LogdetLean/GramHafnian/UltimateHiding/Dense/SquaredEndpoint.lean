import LogdetLean.GramHafnian.UltimateHiding.SquaredRegimeLift
import LogdetLean.GramHafnian.UltimateHiding.Dense.TargetConvergenceFrom

/-!
# Dense squared-rate endpoint from the one-column estimate

This file packages the exact remaining novel analytic obligation.  It does not
assume or axiomize that obligation: `ConcreteDenseSquaredLocalStepAt` is an
explicit proposition.  Once a proof of it is supplied, all telescoping, target
convergence, truncation by one, and dense-regime bookkeeping are kernel
checked here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open LocalAnticoncentration

namespace Dense

/-- The literal local estimate required from the dense score calculation.
It is uniform over normalized Haar presentations, dimensions in the dense
regime, and every ambient index after the large-ambient threshold. -/
def ConcreteDenseSquaredLocalStepAt (C : ℝ) (C0 kappa : ℕ) : Prop :=
  0 <= C ∧
    ∀ (H : UnitaryHaarProbabilityFamily) (N K m : ℕ),
      1 <= N -> N <= K -> K <= m -> C0 * N ^ 2 <= m ->
        kappa * N <= K ->
      probabilityTotalVariationLE
        (denseHaarAmbientLaw H N K m)
        (denseHaarAmbientLaw H N K (m + 1))
        (denseTelescopingRate C N m)

theorem ConcreteDenseSquaredLocalStepAt.constant_nonneg
    {C : ℝ} {C0 kappa : ℕ}
    (h : ConcreteDenseSquaredLocalStepAt C C0 kappa) : 0 <= C :=
  h.1

theorem ConcreteDenseSquaredLocalStepAt.apply
    {C : ℝ} {C0 kappa : ℕ}
    (h : ConcreteDenseSquaredLocalStepAt C C0 kappa)
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hN : 1 <= N) (hNK : N <= K) (hKm : K <= m)
    (hlarge : C0 * N ^ 2 <= m) (hdense : kappa * N <= K) :
    probabilityTotalVariationLE
      (denseHaarAmbientLaw H N K m)
      (denseHaarAmbientLaw H N K (m + 1))
      (denseTelescopingRate C N m) :=
  h.2 H N K m hN hNK hKm hlarge hdense

/-- The local one-column estimate implies the complete very-large dense
branch, including the endpoint `K=M`. -/
theorem veryLargeDenseSquaredBranchAt_of_localStep
    {C : ℝ} {C0 kappa : ℕ}
    (hlocal : ConcreteDenseSquaredLocalStepAt C C0 kappa) :
    VeryLargeDenseSquaredBranchAt C C0 kappa := by
  intro H M N K hN hNK hKM hlarge hdense
  have hNpos : 0 < N := by omega
  have hKpos : 0 < K := hNpos.trans_le hNK
  have hMpos : 1 <= M := by omega
  have hstep : ∀ m, M <= m ->
      probabilityTotalVariationLE
        (denseHaarAmbientLaw H N K m)
        (denseHaarAmbientLaw H N K (m + 1))
        (denseTelescopingRate C N m) := by
    intro m hMm
    exact hlocal.apply H hN hNK (hKM.trans hMm)
      (hlarge.trans hMm) hdense
  have hglobal :=
    probabilityTVLE_dense_telescope_from_to_gaussianTransposeGram_unrestricted
      H C hlocal.constant_nonneg hNpos hKpos hNK hMpos hstep
  letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
    scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
  letI : IsProbabilityMeasure (gaussianTransposeGramLaw N K) :=
    gaussianTransposeGramLaw_isProbability N K
  have hcap := probabilityTotalVariationLE_min_one hglobal
  simp only [ultimateSquaredHidingRate]
  rw [show C * ((N : ℝ) ^ 2 / (M : ℝ)) =
      C * (N : ℝ) ^ 2 / (M : ℝ) by ring]
  exact hcap

/-- The corresponding large-ambient dense branch, including the automatic
intermediate range where the truncated target equals one. -/
theorem largeAmbientDenseSquaredBranchAt_of_localStep
    {C : ℝ} {C0 kappa : ℕ} (hC0 : (C0 : ℝ) <= C)
    (hlocal : ConcreteDenseSquaredLocalStepAt C C0 kappa) :
    LargeAmbientDenseSquaredBranchAt C kappa :=
  LargeAmbientDenseSquaredBranchAt.of_veryLarge hC0
    (veryLargeDenseSquaredBranchAt_of_localStep hlocal)

end Dense

end

end LogdetLean.GramHafnian.UltimateHiding
