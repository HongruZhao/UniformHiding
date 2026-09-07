import LogdetLean.GramHafnian.CircularGaussianVectorWick
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Haar and Gaussian matrix laws for the uniformly-hiding release

This module contains only the common finite-dimensional definitions used by
the hiding theorem: normalized Haar probability, rectangular Haar and
Gaussian matrices, and their transpose-Gram pushforwards.  It deliberately
does not import the historical PRL consequence module or its Shou--Miller--
Galitski asymptotic axiom.

The declarations stay in `CurrentPRL` so the existing hiding proof can reuse
its established notation without any statement conversion.
-/

open scoped BigOperators
open MeasureTheory Set TopologicalSpace

namespace LogdetLean.GramHafnian.CurrentPRL

noncomputable section

/-- Coordinatewise measurable structure for complex matrices. -/
instance hidingReleaseComplexMatrixMeasurableSpace (ι κ : Type*) :
    MeasurableSpace (Matrix ι κ ℂ) := by
  unfold Matrix
  infer_instance

local instance matrixBorelSpace_hidingRelease (N K : ℕ) :
    BorelSpace (Matrix (Fin N) (Fin K) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin N → Fin K → ℂ))

theorem unitaryGroup_carrier_isCompact (M : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin M) ℂ :
      Set (Matrix (Fin M) (Fin M) ℂ)) := by
  let D : Set ℂ := Metric.closedBall 0 1
  have hbox : IsCompact
      (D.matrix : Set (Matrix (Fin M) (Fin M) ℂ)) :=
    (isCompact_closedBall (0 : ℂ) 1).matrix
  refine hbox.of_isClosed_subset ?_ ?_
  · simpa only using
      (isClosed_unitary (R := Matrix (Fin M) (Fin M) ℂ))
  · intro A hA
    rw [Set.mem_matrix]
    intro i j
    simpa [D, Metric.mem_closedBall, dist_zero_right] using
      (entry_norm_bound_of_unitary hA i j)

local instance unitaryGroupCompactSpace_hidingRelease (M : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin M) ℂ) :=
  isCompact_iff_compactSpace.mp (unitaryGroup_carrier_isCompact M)

/-- Haar measure normalized to have mass one on the compact unitary group. -/
def unitaryHaarProbabilityMeasure (M : ℕ) :
    Measure (Matrix.unitaryGroup (Fin M) ℂ) :=
  Measure.haarMeasure
    (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin M) ℂ))

theorem unitaryHaarProbabilityMeasure_univ (M : ℕ) :
    unitaryHaarProbabilityMeasure M Set.univ = 1 := by
  simpa [unitaryHaarProbabilityMeasure] using
    (Measure.haarMeasure_self
      (K₀ := (⊤ : PositiveCompacts
        (Matrix.unitaryGroup (Fin M) ℂ))))

instance unitaryHaarProbabilityMeasure_isProbability (M : ℕ) :
    IsProbabilityMeasure (unitaryHaarProbabilityMeasure M) :=
  ⟨unitaryHaarProbabilityMeasure_univ M⟩

/-- A family of normalized Haar laws. -/
structure UnitaryHaarProbabilityFamily where
  law : (M : ℕ) → Measure (Matrix.unitaryGroup (Fin M) ℂ)
  isProbability : ∀ M, IsProbabilityMeasure (law M)
  isHaar : ∀ M, Measure.IsHaarMeasure (law M)

/-- Canonical normalized Haar family, constructed without an axiom. -/
def canonicalUnitaryHaarProbabilityFamily : UnitaryHaarProbabilityFamily where
  law := unitaryHaarProbabilityMeasure
  isProbability := fun M => unitaryHaarProbabilityMeasure_isProbability M
  isHaar := fun M => by
    unfold unitaryHaarProbabilityMeasure
    infer_instance

/-- The upper-left `N × K` block of an `M × M` unitary. -/
def topLeftUnitaryBlock {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : Matrix (Fin N) (Fin K) ℂ :=
  fun i j =>
    (U : Matrix (Fin M) (Fin M) ℂ)
      (Fin.castLE hNM i) (Fin.castLE hKM j)

@[fun_prop]
theorem measurable_topLeftUnitaryBlock {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M) :
    Measurable (topLeftUnitaryBlock hNM hKM) := by
  unfold topLeftUnitaryBlock
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have hcoe : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ =>
        (U : Matrix (Fin M) (Fin M) ℂ)) :=
    measurable_subtype_coe
  exact (measurable_pi_apply (Fin.castLE hKM j)).comp
    ((measurable_pi_apply (Fin.castLE hNM i)).comp hcoe)

/-- The complex-symmetric transpose-Gram map `G ↦ G Gᵀ`. -/
def rectangularTransposeGram {N K : ℕ}
    (G : Matrix (Fin N) (Fin K) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  G * G.transpose

@[fun_prop]
theorem measurable_rectangularTransposeGram (N K : ℕ) :
    Measurable
      (rectangularTransposeGram :
        Matrix (Fin N) (Fin K) ℂ → Matrix (Fin N) (Fin N) ℂ) := by
  unfold rectangularTransposeGram
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.measurable_sum _ fun a _ => by
    have hi : Measurable
        (fun G : Matrix (Fin N) (Fin K) ℂ => G i a) :=
      (measurable_pi_apply a).comp (measurable_pi_apply i)
    have hj : Measurable
        (fun G : Matrix (Fin N) (Fin K) ℂ => G j a) :=
      (measurable_pi_apply a).comp (measurable_pi_apply j)
    exact hi.mul hj

/-- Literal scaled Haar transpose-Gram matrix `M U_NK U_NKᵀ`. -/
def scaledHaarTransposeGramMatrix {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    (M : ℂ) * rectangularTransposeGram
      (topLeftUnitaryBlock hNM hKM U) i j

@[fun_prop]
theorem measurable_scaledHaarTransposeGramMatrix {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M) :
    Measurable (scaledHaarTransposeGramMatrix hNM hKM) := by
  unfold scaledHaarTransposeGramMatrix
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact measurable_const.mul
    ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp
        ((measurable_rectangularTransposeGram N K).comp
          (measurable_topLeftUnitaryBlock hNM hKM))))

/-- Reinterpret a function-valued rectangular sample as a matrix. -/
def functionToComplexMatrix (N K : ℕ) :
    (Fin N → Fin K → ℂ) → Matrix (Fin N) (Fin K) ℂ :=
  fun G => G

@[fun_prop]
theorem measurable_functionToComplexMatrix (N K : ℕ) :
    Measurable (functionToComplexMatrix N K) := by
  unfold functionToComplexMatrix Matrix
    hidingReleaseComplexMatrixMeasurableSpace
  exact measurable_id

/-- Law of an `N × K` matrix of independent standard circular complex
Gaussians. -/
def standardComplexGaussianRectangularMeasure (N K : ℕ) :
    Measure (Matrix (Fin N) (Fin K) ℂ) :=
  Measure.map (functionToComplexMatrix N K)
    (Measure.pi fun _ : Fin N => circularGaussianVector K)

instance standardComplexGaussianRectangularMeasure_isProbability (N K : ℕ) :
    IsProbabilityMeasure (standardComplexGaussianRectangularMeasure N K) := by
  unfold standardComplexGaussianRectangularMeasure
  letI : IsProbabilityMeasure
      (Measure.pi fun _ : Fin N => circularGaussianVector K) := by
    infer_instance
  exact Measure.isProbabilityMeasure_map
    (measurable_functionToComplexMatrix N K).aemeasurable

/-- Law of `G_NK G_NKᵀ` for a standard Gaussian rectangle. -/
def gaussianTransposeGramLaw (N K : ℕ) :
    Measure (Matrix (Fin N) (Fin N) ℂ) :=
  Measure.map rectangularTransposeGram
    (standardComplexGaussianRectangularMeasure N K)

instance gaussianTransposeGramLaw_isProbability (N K : ℕ) :
    IsProbabilityMeasure (gaussianTransposeGramLaw N K) := by
  unfold gaussianTransposeGramLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_rectangularTransposeGram N K).aemeasurable

/-- Law of `M U_NK U_NKᵀ`, totalized by zero outside `N,K ≤ M`. -/
def scaledHaarTransposeGramLaw
    (H : UnitaryHaarProbabilityFamily) (M N K : ℕ) :
    Measure (Matrix (Fin N) (Fin N) ℂ) :=
  if h : N ≤ M ∧ K ≤ M then
    Measure.map (scaledHaarTransposeGramMatrix h.1 h.2) (H.law M)
  else 0

theorem scaledHaarTransposeGramLaw_isProbability
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M) :
    IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) := by
  rw [scaledHaarTransposeGramLaw, dif_pos ⟨hNM, hKM⟩]
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  exact Measure.isProbabilityMeasure_map
    (measurable_scaledHaarTransposeGramMatrix hNM hKM).aemeasurable

end

end LogdetLean.GramHafnian.CurrentPRL
