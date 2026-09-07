import LogdetLean.GramHafnian.SymmetricGaussianHafnian.LastVertex
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.LiteralCharacteristic
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.SingletonCofactorCharacteristic

/-!
# Singleton characteristic function of the literal symmetric hafnian

The singleton cofactor is the hafnian of an actual independent-edge
principal submatrix.  Its last-vertex Gaussian mixture gives the precise
Fourier kernel involving the previous odd cofactor energy.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 400000

/-- The actual independent-edge hafnian characteristic function is the
Gaussian variance mixture from its literal last-vertex decomposition. -/
theorem integral_exp_re_mul_edgeHafnian_eq_energy_mixture
    (n : ℕ) (t : ℝ) :
    (∫ x : Edge (Fin (n + 1)) → ℂ,
      Complex.exp (((((t : ℂ) * edgeHafnian x).re : ℝ) : ℂ) * Complex.I)
      ∂edgeGaussian (Fin (n + 1))) =
      ∫ A : Edge (Fin n) → ℂ,
        Complex.exp (-(((edgeCofactorEnergy A * t ^ 2 : ℝ) : ℂ) / 4))
        ∂edgeGaussian (Fin n) := by
  let f : ((Edge (Fin n) → ℂ) × (Fin n → ℂ)) → ℂ :=
    fun p ↦ Complex.exp (((((t : ℂ) *
      conditionalCircularLinearForm edgeCofactor p).re : ℝ) : ℂ) * Complex.I)
  have hf : Integrable f
      ((edgeGaussian (Fin n)).prod (standardGaussianProduct (Fin n))) := by
    apply Integrable.of_bound (by
      dsimp [f]
      have hlin : Measurable (conditionalCircularLinearForm
          (edgeCofactor (ι := Fin n))) :=
        measurable_conditionalCircularLinearForm measurable_edgeCofactor
      exact ((Complex.measurable_ofReal.comp
        (Complex.measurable_re.comp (measurable_const.mul hlin))).mul
        measurable_const).cexp.aestronglyMeasurable) 1
    filter_upwards [] with p
    rw [Complex.norm_exp]
    simp
  calc
    (∫ x : Edge (Fin (n + 1)) → ℂ,
      Complex.exp (((((t : ℂ) * edgeHafnian x).re : ℝ) : ℂ) * Complex.I)
      ∂edgeGaussian (Fin (n + 1))) =
        ∫ x : Edge (Fin (n + 1)) → ℂ, f (lastVertexSplit n x)
          ∂edgeGaussian (Fin (n + 1)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [edgeHafnian_eq_lastVertexLinearForm]
    _ = ∫ p, f p
        ∂((edgeGaussian (Fin n)).prod (standardGaussianProduct (Fin n))) := by
      rw [← (measurePreserving_lastVertexSplit n).map_eq]
      symm
      exact integral_map (measurePreserving_lastVertexSplit n).measurable.aemeasurable
        (by rw [(measurePreserving_lastVertexSplit n).map_eq]
            exact hf.aestronglyMeasurable)
    _ = ∫ A, ∫ g, f (A, g)
        ∂standardGaussianProduct (Fin n) ∂edgeGaussian (Fin n) :=
      integral_prod _ hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact integral_exp_re_mul_iidCircularTransposeLinearForm (edgeCofactor A) t

/-- A singleton Fourier coefficient on the last cofactor coordinate gives
the previous cofactor-energy mixture.  This generic dimension form has no
positivity assumption and also covers degenerate small dimensions. -/
theorem edgeCofactorCharacteristic_singleton_last
    (n : ℕ) (t : ℝ) :
    edgeCofactorCharacteristic (Fin (n + 2))
      (singleCoordinate (Fin.last (n + 1)) (t : ℂ)) =
      ∫ A : Edge (Fin n) → ℂ,
        Complex.exp (-(((edgeCofactorEnergy A * t ^ 2 : ℝ) : ℂ) / 4))
        ∂edgeGaussian (Fin n) := by
  have hphase (x : Edge (Fin (n + 2)) → ℂ) :
      edgeCofactorPhaseCharacter (singleCoordinate (Fin.last (n + 1)) (t : ℂ)) x =
        Complex.exp (((((t : ℂ) *
          edgeHafnian (restrictEdges (initialVertexEmbedding (n + 1)) x)).re : ℝ) : ℂ) *
            Complex.I) := by
    unfold edgeCofactorPhaseCharacter edgeCofactorPhase
    simp [singleCoordinate, edgeCofactor_last_eq_restrictedHafnian]
  unfold edgeCofactorCharacteristic
  simp_rw [hphase]
  calc
    _ = ∫ x : Edge (Fin (n + 1)) → ℂ,
        Complex.exp (((((t : ℂ) * edgeHafnian x).re : ℝ) : ℂ) * Complex.I)
        ∂edgeGaussian (Fin (n + 1)) := by
      rw [← (measurePreserving_restrictEdges (initialVertexEmbedding (n + 1))).map_eq]
      symm
      exact integral_map
        (measurePreserving_restrictEdges (initialVertexEmbedding (n + 1))).measurable.aemeasurable
        (by fun_prop)
    _ = _ := integral_exp_re_mul_edgeHafnian_eq_energy_mixture n t

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
