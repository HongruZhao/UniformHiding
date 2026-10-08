import A3.ComplexGaussianScalar
import A3.GSVSpectralSupport

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000

def restrictComplexLinearIsometryEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) : E ≃ₗᵢ[ℝ] F :=
  { e.toLinearEquiv.restrictScalars ℝ with norm_map' := e.norm_map }

def complexGaussianEigenRotate {d : ℕ} {theta : Matrix (Fin d) (Fin d) ℂ}
    (htheta : theta.IsHermitian) : (Fin d → ℂ) ≃ᵐ (Fin d → ℂ) :=
  (MeasurableEquiv.toLp 2 (Fin d → ℂ)).trans
    ((restrictComplexLinearIsometryEquiv htheta.eigenvectorBasis.repr).toMeasurableEquiv.trans
      (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm)

theorem complexGaussianEigenRotate_eq_mulVec {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (z : Fin d → ℂ) :
    complexGaussianEigenRotate htheta z =
      (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ).conjTranspose *ᵥ z := by
  ext i
  change htheta.eigenvectorBasis.repr (toLp 2 z) i = _
  rw [OrthonormalBasis.repr_apply_apply]
  simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    htheta.eigenvectorUnitary_apply, mul_comm]

theorem measurePreserving_complexGaussianEigenRotate {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian) :
    MeasurePreserving (complexGaussianEigenRotate htheta)
      (LogdetLean.GramHafnian.circularGaussianVector d)
      (LogdetLean.GramHafnian.circularGaussianVector d) := by
  let E := EuclideanSpace ℂ (Fin d)
  let c : ℝ := (Real.sqrt 2)⁻¹
  let scale : E → E := fun x ↦ c • x
  let eLp := MeasurableEquiv.toLp 2 (Fin d → ℂ)
  let eReal := restrictComplexLinearIsometryEquiv htheta.eigenvectorBasis.repr
  let eRep := eReal.toMeasurableEquiv
  let muScaled : Measure E := (stdGaussian E).map scale
  have hLp : MeasurePreserving eLp
      (LogdetLean.GramHafnian.circularGaussianVector d) muScaled :=
    ⟨eLp.measurable, map_toLp_circularGaussianVector d⟩
  have hRep : MeasurePreserving eRep muScaled muScaled := by
    refine ⟨eRep.measurable, ?_⟩
    have hscale : Measurable scale := by fun_prop
    have hcomm : eRep ∘ scale = scale ∘ eRep := by
      funext x
      exact eReal.map_smul c x
    dsimp only [muScaled]
    rw [Measure.map_map eRep.measurable hscale, hcomm,
      ← Measure.map_map hscale eRep.measurable]
    change ((stdGaussian E).map eReal).map scale = _
    rw [stdGaussian_map eReal]
  exact (MeasurePreserving.symm eLp hLp).comp (hRep.comp hLp)

theorem complexGaussianEigenRotate_preserves_inner {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (b z : Fin d → ℂ) :
    star (complexGaussianEigenRotate htheta b) ⬝ᵥ complexGaussianEigenRotate htheta z =
      star b ⬝ᵥ z := by
  have h := htheta.eigenvectorBasis.repr.inner_map_map (toLp 2 b) (toLp 2 z)
  change complexGaussianEigenRotate htheta z ⬝ᵥ star (complexGaussianEigenRotate htheta b) =
    z ⬝ᵥ star b at h
  exact (dotProduct_comm _ _).trans (h.trans (dotProduct_comm _ _))

theorem complexGaussianEigenRotate_quadratic {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (z : Fin d → ℂ) :
    star z ⬝ᵥ (theta *ᵥ z) =
      ∑ i, (htheta.eigenvalues i : ℂ) *
        (Complex.normSq (complexGaussianEigenRotate htheta z i) : ℂ) := by
  conv_lhs => rw [htheta.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hleft : star z ᵥ* (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) =
      star ((htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ).conjTranspose *ᵥ z) := by
    simp [Matrix.star_mulVec]
  rw [hleft, ← complexGaussianEigenRotate_eq_mulVec htheta z]
  simp only [Matrix.mulVec_diagonal, dotProduct, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Pi.star_apply, Complex.star_def]
  exact mul_left_comm (star (complexGaussianEigenRotate htheta z i) : ℂ)
    (htheta.eigenvalues i : ℂ) (complexGaussianEigenRotate htheta z i)

end A3Research
