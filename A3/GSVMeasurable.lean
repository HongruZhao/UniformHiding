import A3.Target
import A3.Shared.SpectrumMeasurable

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix MeasureTheory

noncomputable section
namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

theorem continuous_edelmanSuttonFirstGram (n a b : ℕ) :
    Continuous (edelmanSuttonFirstGram (n := n) (a := a) (b := b)) := by
  unfold edelmanSuttonFirstGram
  fun_prop

theorem continuous_edelmanSuttonSecondGram (n a b : ℕ) :
    Continuous (edelmanSuttonSecondGram (n := n) (a := a) (b := b)) := by
  unfold edelmanSuttonSecondGram
  fun_prop

theorem a3_edelmanSuttonFirstGram_posSemidef {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b) :
    (edelmanSuttonFirstGram omega).PosSemidef :=
  posSemidef_conjTranspose_mul_self omega.1

theorem a3_edelmanSuttonSecondGram_posSemidef {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b) :
    (edelmanSuttonSecondGram omega).PosSemidef :=
  posSemidef_conjTranspose_mul_self omega.2

/-- The literal total Gram square root is continuous even at singular samples. -/
theorem continuous_edelmanSuttonTotalGramSqrt (n a b : ℕ) :
    Continuous (edelmanSuttonTotalGramSqrt (n := n) (a := a) (b := b)) := by
  unfold edelmanSuttonTotalGramSqrt
  apply CFC.continuousOn_sqrt.comp_continuous
    ((continuous_edelmanSuttonFirstGram n a b).add
      (continuous_edelmanSuttonSecondGram n a b))
  intro omega
  exact ((a3_edelmanSuttonFirstGram_posSemidef omega).add
    (a3_edelmanSuttonSecondGram_posSemidef omega)).nonneg

/-- The adjugate/determinant definition makes the totalized inverse measurable. -/
theorem measurable_complexMatrix_nonsing_inv (n : ℕ) :
    Measurable (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul
    continuous_id.matrix_adjugate.measurable

theorem measurable_edelmanSuttonJacobiMatrix (n a b : ℕ) :
    Measurable (edelmanSuttonJacobiMatrix (n := n) (a := a) (b := b)) := by
  have hinv := (measurable_complexMatrix_nonsing_inv n).comp
    (continuous_edelmanSuttonTotalGramSqrt n a b).measurable
  unfold edelmanSuttonJacobiMatrix
  exact (hinv.mul (continuous_edelmanSuttonFirstGram n a b).measurable).mul
    (continuous_id.matrix_conjTranspose.measurable.comp hinv)

/-- Global measurability of the exact A3 statistic, including singular inputs. -/
theorem measurable_edelmanSuttonSquaredGSVCoordinates (n a b : ℕ) (beta : ℝ) :
    Measurable (edelmanSuttonSquaredGSVCoordinates n a b beta) := by
  have hspec := A3Research.measurable_hermitian_eigenvalues
    (edelmanSuttonJacobiMatrix (n := n) (a := a) (b := b))
    (fun omega ↦ edelmanSuttonJacobiMatrix_isHermitian omega)
    (measurable_edelmanSuttonJacobiMatrix n a b)
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (Real.continuous_sqrt.measurable.comp
    ((measurable_pi_apply i).comp hspec)).pow_const 2

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
