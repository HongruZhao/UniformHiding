import LogdetLean.GramHafnian.UltimateHiding.Dense.GLConcreteH2Endpoint
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Tactic

/-!
# Signed measure form of the Lemma III.2 derivative transport

The probability law commutation in Lemma III.2 is supplied by the concrete
Gelfand pair endpoint imported above.  This file supplies the distinct
functional analytic step.  It puts the total variation norm on Mathlib finite
signed measures, bundles a linear variation contraction, and proves that such
an operator commutes with every iterated derivative of a variation norm smooth
curve.

No probability total variation surrogate is used here.  The differentiated
objects are genuine `MeasureTheory.SignedMeasure` values.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.ThreePaper.Verification

noncomputable section

/-- A distinct type name for Mathlib finite signed measures equipped below
with their total variation norm. -/
def VariationSignedMeasure (X : Type*) [MeasurableSpace X] :=
  SignedMeasure X

namespace VariationSignedMeasure

variable {X : Type*} [MeasurableSpace X]

/-- Forget the variation norm wrapper. -/
def toSignedMeasure (s : VariationSignedMeasure X) : SignedMeasure X := s

/-- Regard a Mathlib signed measure as an element of the variation norm
space. -/
def ofSignedMeasure (s : SignedMeasure X) : VariationSignedMeasure X := s

@[simp] theorem toSignedMeasure_ofSignedMeasure (s : SignedMeasure X) :
    toSignedMeasure (ofSignedMeasure s) = s := rfl

@[simp] theorem ofSignedMeasure_toSignedMeasure (s : VariationSignedMeasure X) :
    ofSignedMeasure (toSignedMeasure s) = s := rfl

instance : AddCommGroup (VariationSignedMeasure X) :=
  inferInstanceAs (AddCommGroup (SignedMeasure X))

instance : Module ℝ (VariationSignedMeasure X) :=
  inferInstanceAs (Module ℝ (SignedMeasure X))

/-- The total variation norm, namely the mass of the variation measure. -/
def variationNorm (s : VariationSignedMeasure X) : ℝ :=
  (toSignedMeasure s).variation.real univ

instance : Norm (VariationSignedMeasure X) := ⟨variationNorm⟩

@[simp] theorem norm_eq_variation (s : VariationSignedMeasure X) :
    ‖s‖ = (toSignedMeasure s).variation.real univ := rfl

private theorem variationNorm_nonneg (s : VariationSignedMeasure X) :
    0 ≤ ‖s‖ := measureReal_nonneg

private theorem variationNorm_smul (c : ℝ) (s : VariationSignedMeasure X) :
    ‖c • s‖ = ‖c‖ * ‖s‖ := by
  change ((c • toSignedMeasure s).variation).real univ =
    ‖c‖ * (toSignedMeasure s).variation.real univ
  rw [VectorMeasure.variation_smul]
  simp [Real.norm_eq_abs]

private theorem variationNorm_triangle
    (s t : VariationSignedMeasure X) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  letI : IsFiniteMeasure (toSignedMeasure s).variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  letI : IsFiniteMeasure (toSignedMeasure t).variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  change ((toSignedMeasure s + toSignedMeasure t).variation).real univ ≤
    (toSignedMeasure s).variation.real univ +
      (toSignedMeasure t).variation.real univ
  calc
    ((toSignedMeasure s + toSignedMeasure t).variation).real univ ≤
        ((toSignedMeasure s).variation +
          (toSignedMeasure t).variation).real univ := by
      exact ENNReal.toReal_mono (by finiteness)
        (VectorMeasure.variation_add_le univ)
    _ = (toSignedMeasure s).variation.real univ +
        (toSignedMeasure t).variation.real univ := by
      exact measureReal_add_apply

private theorem variationNorm_eq_zero_iff
    (s : VariationSignedMeasure X) : ‖s‖ = 0 ↔ s = 0 := by
  constructor
  · intro h
    letI : IsFiniteMeasure (toSignedMeasure s).variation := by
      rw [← SignedMeasure.totalVariation_eq_variation]
      infer_instance
    have hu : (toSignedMeasure s).variation univ = 0 :=
      (measureReal_eq_zero_iff (by finiteness)).1 h
    have hv : (toSignedMeasure s).variation = 0 :=
      Measure.measure_univ_eq_zero.mp hu
    have hs : toSignedMeasure s = 0 :=
      VectorMeasure.variation_eq_zero.mp hv
    exact hs
  · rintro rfl
    have hv : (0 : SignedMeasure X).variation = 0 :=
      VectorMeasure.variation_eq_zero.mpr rfl
    change (toSignedMeasure (0 : VariationSignedMeasure X)).variation.real univ = 0
    rw [show toSignedMeasure (0 : VariationSignedMeasure X) = 0 from rfl,
      hv]
    exact measureReal_zero_apply univ

/-- The normed real vector space structure induced by total variation. -/
def variationNormedSpaceCore :
    NormedSpace.Core ℝ (VariationSignedMeasure X) where
  norm_nonneg := variationNorm_nonneg
  norm_smul := variationNorm_smul
  norm_triangle := variationNorm_triangle
  norm_eq_zero_iff := variationNorm_eq_zero_iff

instance : NormedAddCommGroup (VariationSignedMeasure X) :=
  NormedAddCommGroup.ofCore variationNormedSpaceCore

instance : NormedSpace ℝ (VariationSignedMeasure X) :=
  NormedSpace.ofCore variationNormedSpaceCore

end VariationSignedMeasure

/-- A bounded linear extension of a Markov operator on finite signed
measures, bundled with the sharp total variation contraction. -/
structure VariationMarkovOperator (X : Type*) [MeasurableSpace X] where
  toLinearMap : VariationSignedMeasure X →ₗ[ℝ] VariationSignedMeasure X
  contractive : ∀ s, ‖toLinearMap s‖ ≤ ‖s‖

namespace VariationMarkovOperator

variable {X : Type*} [MeasurableSpace X]

instance : CoeFun (VariationMarkovOperator X)
    (fun _ ↦ VariationSignedMeasure X → VariationSignedMeasure X) :=
  ⟨fun T ↦ T.toLinearMap⟩

@[simp] theorem map_add (T : VariationMarkovOperator X)
    (s t : VariationSignedMeasure X) : T (s + t) = T s + T t :=
  T.toLinearMap.map_add s t

@[simp] theorem map_smul (T : VariationMarkovOperator X)
    (c : ℝ) (s : VariationSignedMeasure X) : T (c • s) = c • T s :=
  T.toLinearMap.map_smul c s

/-- The continuous linear map carried by a variation contractive Markov
extension. -/
def toContinuousLinearMap (T : VariationMarkovOperator X) :
    VariationSignedMeasure X →L[ℝ] VariationSignedMeasure X :=
  T.toLinearMap.mkContinuous 1 (fun s ↦ by simpa using T.contractive s)

@[simp] theorem toContinuousLinearMap_apply
    (T : VariationMarkovOperator X) (s : VariationSignedMeasure X) :
    T.toContinuousLinearMap s = T s := rfl

theorem toContinuousLinearMap_norm_le_one (T : VariationMarkovOperator X) :
    ‖T.toContinuousLinearMap‖ ≤ 1 :=
  T.toLinearMap.mkContinuous_norm_le zero_le_one
    (fun s ↦ by simpa using T.contractive s)

/-- Paper Eq. `hide-commute-contraction`: the signed extension contracts the
total variation norm. -/
theorem eq_hide_commute_contraction
    (T : VariationMarkovOperator X) (s : VariationSignedMeasure X) :
    ‖T s‖ ≤ ‖s‖ :=
  T.contractive s

/-- Paper Eq. `hide-commute-derivative`: a fixed bounded linear Markov
operator passes through every derivative of a variation norm `C^r` curve on
an open real set, and the resulting derivative obeys the same sharp
variation bound. -/
theorem eq_hide_commute_derivative
    (T : VariationMarkovOperator X)
    (f : ℝ → VariationSignedMeasure X)
    (I : Set ℝ) (hI : IsOpen I) (r j : ℕ)
    (hf : ContDiffOn ℝ r f I) (hj : j ≤ r)
    (s : ℝ) (hs : s ∈ I) :
    iteratedDerivWithin j (fun u ↦ T (f u)) I s =
        T (iteratedDerivWithin j f I s) ∧
      ‖iteratedDerivWithin j (fun u ↦ T (f u)) I s‖ ≤
        ‖iteratedDerivWithin j f I s‖ := by
  let L := T.toContinuousLinearMap
  have hF := L.iteratedFDerivWithin_comp_left
    (hf s hs) hI.uniqueDiffOn hs (by exact_mod_cast hj)
  have hderiv :
      iteratedDerivWithin j (fun u ↦ T (f u)) I s =
        T (iteratedDerivWithin j f I s) := by
    change
      (iteratedFDerivWithin ℝ j (L ∘ f) I s)
          (fun _ : Fin j ↦ 1) =
        L ((iteratedFDerivWithin ℝ j f I s)
          (fun _ : Fin j ↦ 1))
    rw [hF]
    rfl
  exact ⟨hderiv, hderiv ▸ T.contractive _⟩

end VariationMarkovOperator

end

end LogdetLean.GramHafnian.ThreePaper.Verification
