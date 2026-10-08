import A3.HermitianAtlasFiber

open Set Function MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

theorem continuous_hermitianVandermonde (n : ℕ) :
    Continuous (hermitianVandermonde : (Fin n → ℝ) → ℝ) := by
  unfold hermitianVandermonde
  fun_prop

theorem hermitianVandermonde_nonneg (lambda : Fin n → ℝ) :
    0 ≤ hermitianVandermonde lambda := Finset.prod_nonneg fun _ _ ↦ abs_nonneg _

theorem hermitianVandermonde_ne_zero_iff_injective (lambda : Fin n → ℝ) :
    hermitianVandermonde lambda ≠ 0 ↔ Injective lambda := by
  classical
  unfold hermitianVandermonde
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (h ⟨(i, j), hlt⟩ (Finset.mem_univ _)) (by simp [hij])
    · exact (h ⟨(j, i), hgt⟩ (Finset.mem_univ _)) (by simp [hij])
  · intro h ij _
    exact abs_ne_zero.mpr (sub_ne_zero.mpr (fun he ↦ ij.2.ne (h he.symm)))

theorem hermitianVandermonde_pos_iff_injective (lambda : Fin n → ℝ) :
    0 < hermitianVandermonde lambda ↔ Injective lambda := by
  rw [← hermitianVandermonde_ne_zero_iff_injective]
  exact ⟨ne_of_gt, fun h ↦ lt_of_le_of_ne (hermitianVandermonde_nonneg lambda) h.symm⟩

def hermitianFlatEigenvalueDensity (n : ℕ) (K : Type*) [RCLike K]
    (lambda : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (hermitianVandermonde lambda ^ Module.finrank ℝ K)

theorem measurable_hermitianFlatEigenvalueDensity (n : ℕ) (K : Type*) [RCLike K] :
    Measurable (hermitianFlatEigenvalueDensity n K) :=
  ((continuous_hermitianVandermonde n).pow _).measurable.ennreal_ofReal

def hermitianFlatEigenvalueRadialMeasure (n : ℕ) (K : Type*) [RCLike K] :
    Measure (Fin n → ℝ) := volume.withDensity (hermitianFlatEigenvalueDensity n K)

theorem ae_mem_regularHermitianRadii_radialMeasure (n : ℕ) (K : Type*) [RCLike K] :
    ∀ᵐ lambda ∂hermitianFlatEigenvalueRadialMeasure n K,
      lambda ∈ regularHermitianRadii n := by
  unfold hermitianFlatEigenvalueRadialMeasure
  rw [ae_withDensity_iff (measurable_hermitianFlatEigenvalueDensity n K)]
  filter_upwards [] with lambda hdensity
  apply (hermitianVandermonde_ne_zero_iff_injective lambda).mp
  intro hz
  apply hdensity
  simp [hermitianFlatEigenvalueDensity, hz, (Module.finrank_pos (R := ℝ) (M := K)).ne']

theorem regularHermitian_radial_withDensity_eq_flat (n : ℕ) (K : Type*) [RCLike K] :
    (volume.restrict (regularHermitianRadii n)).withDensity
      (hermitianFlatEigenvalueDensity n K) = hermitianFlatEigenvalueRadialMeasure n K := by
  have he := restrict_eq_self_of_ae_mem (ae_mem_regularHermitianRadii_radialMeasure n K)
  rw [hermitianFlatEigenvalueRadialMeasure,
    restrict_withDensity (isOpen_regularHermitianRadii n).measurableSet] at he
  exact he

theorem hermitianFlatEigenvalueDensity_real (lambda : Fin n → ℝ) :
    hermitianFlatEigenvalueDensity n ℝ lambda = ENNReal.ofReal (hermitianVandermonde lambda) := by
  simp [hermitianFlatEigenvalueDensity]

theorem hermitianFlatEigenvalueDensity_complex (lambda : Fin n → ℝ) :
    hermitianFlatEigenvalueDensity n ℂ lambda =
      ENNReal.ofReal (hermitianVandermonde lambda ^ 2) := by
  simp [hermitianFlatEigenvalueDensity, Complex.finrank_real_complex]

end A3Research
