import LogdetLean.GramHafnian.UltimateHiding.Sparse.CircularGaussianDensityBasic
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19DensityLimit

/-!
# Elementary transports from an unscaled Haar-corner density

These adapters isolate the `sqrt M` coordinate dilation and the conversion
from the ENNReal density to its ordinary nonnegative real representative.
Their source density equality is an explicit theorem argument, so the same
transport can be used with the internally proved Jiang formula.
-/

open MeasureTheory Matrix
open scoped ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open LocalAnticoncentration

/-- Transport any proof of the unscaled Jiang density through entrywise
multiplication by `sqrt M`. -/
theorem jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_of_unscaled
    {M N K : ℕ} (hM : 0 < M)
    (hunscaled :
      jiangUnscaledTallHaarCornerLaw M K N =
        (complexRectangularLebesgueVolume K N).withDensity
          (jiangUnscaledTallHaarCornerPDF M K N)) :
    jiangSqrtScaledTallHaarCornerLaw M K N =
      (complexRectangularLebesgueVolume K N).withDensity
        (jiangSqrtScaledTallHaarCornerPDF M K N) := by
  let e := rectangularSqrtScaleMeasurableEquiv M K N hM
  have he : (e : Matrix (Fin K) (Fin N) ℂ →
      Matrix (Fin K) (Fin N) ℂ) =
      fun X ↦ Real.sqrt (M : ℝ) • X := by
    rfl
  have hesymm : (e.symm : Matrix (Fin K) (Fin N) ℂ →
      Matrix (Fin K) (Fin N) ℂ) =
      fun Z ↦ (Real.sqrt (M : ℝ))⁻¹ • Z := by
    rfl
  rw [jiangSqrtScaledTallHaarCornerLaw, hunscaled, ← he]
  rw [map_measurableEquiv_withDensity_localAnticoncentration e
    (complexRectangularLebesgueVolume K N)
    (jiangUnscaledTallHaarCornerPDF M K N)
    (measurable_jiangUnscaledTallHaarCornerPDF M K N)]
  rw [map_rectangularSqrtScale_complexRectangularLebesgueVolume hM,
    withDensity_smul_measure,
    ← withDensity_smul
      (ENNReal.ofReal (((M : ℝ)⁻¹) ^ (K * N)))
      ((measurable_jiangUnscaledTallHaarCornerPDF M K N).comp
        e.symm.measurable)]
  congr 1

/-- Real-density form of the preceding transport. -/
theorem jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_of_unscaled
    {M N K : ℕ} (hM : 0 < M)
    (hunscaled :
      jiangUnscaledTallHaarCornerLaw M K N =
        (complexRectangularLebesgueVolume K N).withDensity
          (jiangUnscaledTallHaarCornerPDF M K N)) :
    jiangSqrtScaledTallHaarCornerLaw M K N =
      (complexRectangularLebesgueVolume K N).withDensity
        (fun Z ↦ ENNReal.ofReal
          (jiangSqrtScaledTallHaarCornerRealPDF M K N Z)) := by
  rw [jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_of_unscaled hM hunscaled]
  congr 1
  funext Z
  exact jiangSqrtScaledTallHaarCornerPDF_eq_ofReal M K N Z

#print axioms jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_of_unscaled
#print axioms jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_of_unscaled

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
