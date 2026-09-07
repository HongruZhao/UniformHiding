import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredJetTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredWeakGeneratorInterface
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16MatrixExponentialContinuity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Topology.CompactOpen

/-!
# The literal centered jets as fixed-direction `L1` pullback orbits

Assuming only the integrability and measure-preservation fields of the
weak-generator facts, this module packages each literal jet in `L1` and
identifies every time slice with pullback of its base representative.  It
does not use boundary continuity, H5, or an event.
-/

open MeasureTheory
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

abbrev H16CenteredCoordinateL1 (N : ℕ) :=
  ComplexSymmetricCoordinates N →₁[
    complexSymmetricCoordinateVolume N] ℝ

@[fun_prop]
theorem continuous_complexSymmetricCoordinatesOfMatrix (N : ℕ) :
    Continuous (complexSymmetricCoordinatesOfMatrix (N := N)) := by
  refine continuous_pi fun ij ↦ ?_
  exact (continuous_apply ij.1.2).comp (continuous_apply ij.1.1)

@[fun_prop]
theorem continuous_complexSymmetricMatrixOfCoordinates (N : ℕ) :
    Continuous (complexSymmetricMatrixOfCoordinates (N := N)) := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  by_cases hij : i ≤ j
  · simpa only [complexSymmetricMatrixOfCoordinates, dif_pos hij] using
      (continuous_apply (⟨(i, j), hij⟩ :
        ComplexSymmetricCoordinateIndex N))
  · simpa only [complexSymmetricMatrixOfCoordinates, dif_neg hij] using
      (continuous_apply (⟨(j, i), le_of_lt (lt_of_not_ge hij)⟩ :
        ComplexSymmetricCoordinateIndex N))

private theorem continuous_complex_matrix_mul (N : ℕ) :
    Continuous (fun p : ConcreteMatrixState N × ConcreteMatrixState N ↦
      p.1 * p.2) := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  simp only [Matrix.mul_apply]
  refine continuous_finsetSum _ fun k _ ↦ ?_
  fun_prop

private theorem continuous_complex_matrix_transpose (N : ℕ) :
    Continuous (Matrix.transpose :
      ConcreteMatrixState N → ConcreteMatrixState N) := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  exact (continuous_apply i).comp (continuous_apply j)

/-- The inverse flow as a continuous self-map of coordinate space. -/
def h16CenteredInverseCoordinateFlowCM {N : ℕ}
    (v : ComplexUnitSphere N) (t : ℝ) :
    C(ComplexSymmetricCoordinates N, ComplexSymmetricCoordinates N) where
  toFun := h16CenteredCoordinateFlow v (-t)
  continuous_toFun := by
    unfold h16CenteredCoordinateFlow transposeCongruenceFlowCoordinates
    unfold transposeCongruenceFlow transposeCongruence
    fun_prop

theorem continuous_h16CenteredInverseCoordinateFlowCM_of_matrixExp
    {N : ℕ} (v : ComplexUnitSphere N)
    (hexpCurve : H16MatrixExponentialCurveContinuous N
      (concreteCenteredOrbitalDirection N v)) :
    Continuous (h16CenteredInverseCoordinateFlowCM v) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × ComplexSymmetricCoordinates N ↦
    h16CenteredCoordinateFlow v (-p.1) p.2)
  unfold h16CenteredCoordinateFlow transposeCongruenceFlowCoordinates
    transposeCongruenceFlow transposeCongruence
  let A := concreteCenteredOrbitalDirection N v
  have hexp : Continuous (fun p : ℝ × ComplexSymmetricCoordinates N ↦
      NormedSpace.exp (((-p.1 : ℝ) : ℂ) • A)) := by
    simpa [Function.comp_def, A] using
      hexpCurve.comp (continuous_neg.comp continuous_fst)
  have hmatrix : Continuous (fun p : ℝ × ComplexSymmetricCoordinates N ↦
      complexSymmetricMatrixOfCoordinates p.2) :=
    (continuous_complexSymmetricMatrixOfCoordinates N).comp continuous_snd
  have hleft : Continuous (fun p : ℝ × ComplexSymmetricCoordinates N ↦
      NormedSpace.exp (((-p.1 : ℝ) : ℂ) • A) *
        complexSymmetricMatrixOfCoordinates p.2) :=
    (continuous_complex_matrix_mul N).comp (hexp.prodMk hmatrix)
  have htranspose : Continuous (fun p : ℝ × ComplexSymmetricCoordinates N ↦
      Matrix.transpose (NormedSpace.exp (((-p.1 : ℝ) : ℂ) • A))) :=
    (continuous_complex_matrix_transpose N).comp hexp
  exact (continuous_complexSymmetricCoordinatesOfMatrix N).comp <|
    (continuous_complex_matrix_mul N).comp (hleft.prodMk htranspose)

/-- The canonical `L1` class represented by a literal jet. -/
noncomputable def h16CenteredJetLpOfWeak
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    H16CenteredCoordinateL1 N :=
  (W.jet_integrable r v t).toL1
    (h16CenteredTransportJet N K r v t)

theorem h16CenteredJetLpOfWeak_coeFn_ae
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    (fun x ↦ h16CenteredJetLpOfWeak W r v t x) =ᵐ[
        complexSymmetricCoordinateVolume N]
      h16CenteredTransportJet N K r v t :=
  Integrable.coeFn_toL1 (W.jet_integrable r v t)

/-- The time-`t` `L1` jet is exactly pullback of its time-zero class. -/
theorem h16CenteredJetLpOfWeak_eq_pullback_zero
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    h16CenteredJetLpOfWeak W r v t =
      Lp.compMeasurePreserving
        (h16CenteredCoordinateFlow v (-t))
        (W.coordinate_measurePreserving v (-t))
        (h16CenteredJetLpOfWeak W r v 0) := by
  apply Lp.ext
  filter_upwards [h16CenteredJetLpOfWeak_coeFn_ae W r v t,
    Lp.coeFn_compMeasurePreserving
      (h16CenteredJetLpOfWeak W r v 0)
      (W.coordinate_measurePreserving v (-t)),
    (W.coordinate_measurePreserving v (-t)).quasiMeasurePreserving.ae
      (h16CenteredJetLpOfWeak_coeFn_ae W r v 0)]
      with x htx hpull hzero
  rw [htx, hpull]
  change h16CenteredTransportJet N K r v t x =
    h16CenteredJetLpOfWeak W r v 0
      (h16CenteredCoordinateFlow v (-t) x)
  rw [hzero]
  exact h16CenteredTransportJet_eq_zero_pullback r v t x

/-- Each fixed-direction jet orbit is strongly continuous in `L1`. -/
theorem continuous_h16CenteredJetLpOfWeak_fixedDirection_of_matrixExp
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N)
    (hexpCurve : H16MatrixExponentialCurveContinuous N
      (concreteCenteredOrbitalDirection N v)) :
    Continuous (fun t : ℝ ↦ h16CenteredJetLpOfWeak W r v t) := by
  letI : IsLocallyFiniteMeasure (complexSymmetricCoordinateVolume N) := by
    rw [show complexSymmetricCoordinateVolume N =
        (volume : Measure (ComplexSymmetricCoordinates N)) by
      unfold complexSymmetricCoordinateVolume
      exact MeasureTheory.volume_pi.symm]
    infer_instance
  have hflow : Continuous (h16CenteredInverseCoordinateFlowCM v) :=
    continuous_h16CenteredInverseCoordinateFlowCM_of_matrixExp v hexpCurve
  have hpull : Continuous (fun t : ℝ ↦
      Lp.compMeasurePreserving
        (h16CenteredInverseCoordinateFlowCM v t)
        (W.coordinate_measurePreserving v (-t))
        (h16CenteredJetLpOfWeak W r v 0)) := by
    exact continuous_const.compMeasurePreservingLp hflow
      (fun t ↦ W.coordinate_measurePreserving v (-t))
      (by norm_num)
  apply hpull.congr
  intro t
  exact (h16CenteredJetLpOfWeak_eq_pullback_zero W r v t).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
