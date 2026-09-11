import GBSHiding.AllInputs
import LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy
import LogdetLean.GramHafnian.ThreePaper.UniformMatrixHidingEndpointsAudit
import LogdetLean.GramHafnian.ThreePaper.RelativeAccuracyEndpointsAudit
import GBSHiding.OptimizedCertificates
import GBSHiding.Completion

/-!
# Uniform hiding and the two routes

Public statements for the merged Quantum manuscript. The underlying proofs
retain their original namespaces so that the source refactor does not rename
thousands of checked dependencies. See the current local execution receipts.
See README.md and docs/ASSUMPTIONS.md before interpreting these declarations.
-/

open MeasureTheory
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding

namespace GBSHiding

noncomputable section

/-- Original finite product-law theorem, conditional on the four recorded literature inputs. -/
theorem uniformHiding : UniformProductMatrixHidingSquaredAt 615172 :=
  LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding.matrixLaw

/-- The normalized statement for `1 ≤ N ≤ K ≤ M`. -/
theorem normalizedHiding
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M) :
    probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (min 1 (615172 * ultimateSquaredHidingRate M N)) :=
  LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding.normalizedMatrixLaw
    H M N K hN hNK hKM

/-- Finite-Haar local bound obtained by combining the hiding and Gaussian proofs. -/
theorem finiteHaarSmallBall
    (H : UnitaryHaarProbabilityFamily)
    {M n K : ℕ} (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    (scaledHaarGramHafnianLaw H M n K).real
        (shiftedComplexDisk z (eps * gramHafnianSigma K n)) ≤
      min 1
        (shiftedAnticoncentrationConstant K n * eps ^ 2 +
          615172 * ultimateSquaredHidingRate M (2 * n)) :=
  LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.finiteHaarShiftedSmallBall
    H hn hK hKM z eps heps

end
end GBSHiding

#print axioms GBSHiding.uniformHiding
#print axioms GBSHiding.normalizedHiding
#print axioms GBSHiding.finiteHaarSmallBall
#print axioms GBSHiding.lowerBound_optimizedCertificate

#print axioms GBSHiding.normalizedHidingAllInputs
#print axioms GBSHiding.observableHidingAllInputs

#print axioms GBSHiding.orderedFixedPatternPanelAllInputs
