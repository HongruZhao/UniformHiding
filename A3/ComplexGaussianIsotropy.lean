import A3.WishartGaussianDensity
import A3.GaussianMatrixRank
import A4.TriangularGaussianLaplace

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators

noncomputable section
namespace A3Research

def complexRealOrthonormalBasis (d : ℕ) :
    OrthonormalBasis ((i : Fin d) × Fin 2) ℝ (EuclideanSpace ℂ (Fin d)) :=
  Pi.orthonormalBasis fun _ : Fin d ↦ Complex.orthonormalBasisOneI

def packComplexCoordinates (d : ℕ) (x : ((i : Fin d) × Fin 2) → ℝ) : Fin d → ℂ :=
  fun i ↦ (x ⟨i, 0⟩ : ℂ) + (x ⟨i, 1⟩ : ℂ) * Complex.I

theorem complexRealOrthonormalBasis_reconstruction (d : ℕ)
    (x : ((i : Fin d) × Fin 2) → ℝ) :
    (complexRealOrthonormalBasis d).repr.symm (toLp 2 x) =
      toLp 2 (packComplexCoordinates d x) := by
  apply (complexRealOrthonormalBasis d).repr.injective
  ext p
  rcases p with ⟨i, j⟩
  fin_cases j <;> simp [complexRealOrthonormalBasis, packComplexCoordinates,
    Pi.orthonormalBasis_repr]

theorem map_packComplexScalar_halfGaussian :
    (Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 (1 / 2)).map
      (fun x : Fin 2 → ℝ ↦ (x 0 : ℂ) + (x 1 : ℂ) * Complex.I) =
        LogdetLean.GramHafnian.circularGaussian := by
  rw [circularGaussian_eq_map_halfGaussian,
    ← (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ gaussianReal 0 (1 / 2))).map_eq,
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).measurable]
  congr 1
  funext x
  apply Complex.ext <;> simp [Function.comp_def, MeasurableEquiv.piFinTwo_apply]

theorem map_packComplexCoordinates_halfGaussian (d : ℕ) :
    (Measure.pi fun _ : ((i : Fin d) × Fin 2) ↦ gaussianReal 0 (1 / 2)).map
      (packComplexCoordinates d) = LogdetLean.GramHafnian.circularGaussianVector d := by
  let curry := MeasurableEquiv.piCurry (fun _ : Fin d ↦ fun _ : Fin 2 ↦ ℝ)
  have hcurry : (Measure.pi fun _ : ((i : Fin d) × Fin 2) ↦ gaussianReal 0 (1 / 2)).map
      curry = Measure.pi (fun _ : Fin d ↦ Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 (1 / 2)) := by
    rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
    simp_rw [← Measure.infinitePi_eq_pi]
    exact Measure.infinitePi_map_piCurry (fun _ : Fin d ↦ fun _ : Fin 2 ↦ gaussianReal 0 (1 / 2))
  have hpoint : packComplexCoordinates d =
      (fun x : Fin d → Fin 2 → ℝ ↦ fun i ↦ (x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) ∘ curry := rfl
  rw [hpoint, ← Measure.map_map (by fun_prop) curry.measurable, hcurry]
  rw [Measure.pi_map_pi (fun _ ↦ (show Measurable
    (fun x : Fin 2 → ℝ ↦ (x 0 : ℂ) + (x 1 : ℂ) * Complex.I) by fun_prop).aemeasurable)]
  simp only [map_packComplexScalar_halfGaussian, LogdetLean.GramHafnian.circularGaussianVector]

/-- The literal circular vector is the real isotropic Gaussian at variance one half. -/
theorem map_toLp_circularGaussianVector (d : ℕ) :
    (LogdetLean.GramHafnian.circularGaussianVector d).map (toLp 2) =
      (stdGaussian (EuclideanSpace ℂ (Fin d))).map
        (fun x : EuclideanSpace ℂ (Fin d) ↦ (Real.sqrt 2)⁻¹ • x) := by
  let J := (i : Fin d) × Fin 2
  let B := complexRealOrthonormalBasis d
  let packLp : (J → ℝ) → EuclideanSpace ℂ (Fin d) :=
    fun x ↦ B.repr.symm (toLp 2 x)
  have hpack : packLp = (toLp 2) ∘ packComplexCoordinates d := by
    funext x
    exact complexRealOrthonormalBasis_reconstruction d x
  have hstd : (Measure.pi fun _ : J ↦ gaussianReal 0 1).map packLp =
      stdGaussian (EuclideanSpace ℂ (Fin d)) := by
    rw [stdGaussian_eq_map_pi_orthonormalBasis B]
    congr 1
    funext x
    dsimp only [packLp]
    rw [← B.sum_repr (B.repr.symm (toLp 2 x))]
    simp
  have hhalf : (Measure.pi fun _ : J ↦ gaussianReal 0 (1 / 2)) =
      (Measure.pi fun _ : J ↦ gaussianReal 0 1).map
        (fun x : J → ℝ ↦ fun i ↦ (Real.sqrt 2)⁻¹ * x i) := by
    rw [Measure.pi_map_pi (fun _ ↦ (show Measurable
      (fun x : ℝ ↦ (Real.sqrt 2)⁻¹ * x) by fun_prop).aemeasurable)]
    simp only [A4Research.map_invSqrtTwo_gaussian]
  rw [← map_packComplexCoordinates_halfGaussian d,
    Measure.map_map (by fun_prop) (by unfold packComplexCoordinates; fun_prop), ← hpack,
    hhalf, Measure.map_map (by dsimp [packLp]; fun_prop) (by fun_prop)]
  rw [← hstd, Measure.map_map (by fun_prop) (by dsimp [packLp]; fun_prop)]
  congr 1
  funext x
  exact map_smul B.repr.symm (Real.sqrt 2)⁻¹ (toLp 2 x)

end A3Research
