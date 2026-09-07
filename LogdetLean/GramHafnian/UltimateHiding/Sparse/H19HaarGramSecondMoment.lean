import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_HaarLastColumnUniform
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveSecondMoment
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19JiangRawDensity
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

/-!
# Internal second Gram moment for a scaled Haar corner

This file proves the fourth-coordinate calculation needed by the direct
quantitative H19 route.  It uses only normalized Haar invariance, unitarity,
and the internally proved second projective moment of a uniform complex
sphere direction.
-/

open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

local instance unitaryGroupCompactSpaceH19GramMoment (M : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin M) ℂ) :=
  isCompact_iff_compactSpace.mp (unitaryGroup_carrier_isCompact M)

/-! ## An arbitrary Haar column is a uniform sphere direction -/

/-- The permutation unitary which swaps a specified column with the final
column. -/
def haarColumnSwapUnitary {M : ℕ} (hM : 1 ≤ M) (j : Fin M) :
    Matrix.unitaryGroup (Fin M) ℂ := by
  let σ : Equiv.Perm (Fin M) := Equiv.swap (haarLastColumnIndex hM) j
  refine ⟨σ.permMatrix ℂ, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp [σ]

/-- The `j`th Haar column, represented by transporting the last-column map
through a fixed right permutation. -/
def haarColumnSphere {M : ℕ} (hM : 1 ≤ M) (j : Fin M) :
    Matrix.unitaryGroup (Fin M) ℂ → ComplexUnitSphere M :=
  fun U ↦ haarLastColumnSphere hM (U * haarColumnSwapUnitary hM j)

theorem measurable_unitary_mul_right_h19Gram {M : ℕ}
    (V : Matrix.unitaryGroup (Fin M) ℂ) :
    Measurable (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦ U * V) := by
  apply Measurable.subtype_mk
  change Measurable
    (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
      (U : Matrix (Fin M) (Fin M) ℂ) *
        (V : Matrix (Fin M) (Fin M) ℂ))
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ ↦ ?_
  have hcoe : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        (U : Matrix (Fin M) (Fin M) ℂ)) :=
    measurable_subtype_coe
  exact ((measurable_pi_apply k).comp
    ((measurable_pi_apply i).comp hcoe)).mul measurable_const

theorem measurable_unitary_inv_h19Gram (M : ℕ) :
    Measurable (Inv.inv : Matrix.unitaryGroup (Fin M) ℂ →
      Matrix.unitaryGroup (Fin M) ℂ) := by
  apply Measurable.subtype_mk
  change Measurable
    (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
      star (U : Matrix (Fin M) (Fin M) ℂ))
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  have hcoe : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        (U : Matrix (Fin M) (Fin M) ℂ)) :=
    measurable_subtype_coe
  exact Complex.continuous_conj.measurable.comp
    ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp hcoe))

theorem measurable_haarColumnSphere {M : ℕ} (hM : 1 ≤ M) (j : Fin M) :
    Measurable (haarColumnSphere hM j) := by
  exact (measurable_haarLastColumnSphere hM).comp
    (measurable_unitary_mul_right_h19Gram (haarColumnSwapUnitary hM j))

@[simp]
theorem haarColumnSphere_apply {M : ℕ} (hM : 1 ≤ M)
    (j i : Fin M) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    (haarColumnSphere hM j U).1 i =
      (U : Matrix (Fin M) (Fin M) ℂ) i j := by
  rw [haarColumnSphere, haarLastColumnSphere_apply]
  change
    (((U : Matrix (Fin M) (Fin M) ℂ) *
      (Equiv.swap (haarLastColumnIndex hM) j).permMatrix ℂ)
        i (haarLastColumnIndex hM)) = _
  have hvec := Matrix.vecMul_permMatrix
    (R := ℂ) (σ := Equiv.swap (haarLastColumnIndex hM) j)
    (v := fun k : Fin M ↦ (U : Matrix (Fin M) (Fin M) ℂ) i k)
  have happ := congrFun hvec (haarLastColumnIndex hM)
  change
    ((fun k : Fin M ↦ (U : Matrix (Fin M) (Fin M) ℂ) i k) ᵥ*
      (Equiv.swap (haarLastColumnIndex hM) j).permMatrix ℂ)
        (haarLastColumnIndex hM) = _
  simpa using happ

/-- Every fixed column of a normalized Haar unitary has normalized uniform
surface law on the complex unit sphere. -/
theorem map_haarColumnSphere_unitaryHaarProbabilityMeasure
    {M : ℕ} (hM : 1 ≤ M) (j : Fin M) :
    Measure.map (haarColumnSphere hM j)
        (unitaryHaarProbabilityMeasure M) =
      complexUnitSphereProbabilityMeasure M := by
  calc
    Measure.map (haarColumnSphere hM j)
        (unitaryHaarProbabilityMeasure M) =
      Measure.map (haarLastColumnSphere hM)
        (Measure.map
          (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
            U * haarColumnSwapUnitary hM j)
          (unitaryHaarProbabilityMeasure M)) := by
            change Measure.map
                (haarLastColumnSphere hM ∘
                  fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
                    U * haarColumnSwapUnitary hM j)
                (unitaryHaarProbabilityMeasure M) = _
            rw [Measure.map_map
              (measurable_haarLastColumnSphere hM)
              (measurable_unitary_mul_right_h19Gram
                (haarColumnSwapUnitary hM j))]
    _ = Measure.map (haarLastColumnSphere hM)
        (unitaryHaarProbabilityMeasure M) := by
      rw [map_unitaryHaarProbabilityMeasure_mul_right_H19]
    _ = complexUnitSphereProbabilityMeasure M :=
      map_haarLastColumnSphere_unitaryHaarProbabilityMeasure hM

theorem integrable_haarColumn_projective_entry
    {M : ℕ} (hM : 1 ≤ M) (j i₁ i₂ : Fin M) :
    Integrable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        complexRankOneProjection (haarColumnSphere hM j U) i₁ i₂)
      (unitaryHaarProbabilityMeasure M) := by
  let g : ComplexUnitSphere M → ℂ := fun v ↦
    complexRankOneProjection v i₁ i₂
  have hmap := map_haarColumnSphere_unitaryHaarProbabilityMeasure hM j
  have hgmap : Integrable g
      (Measure.map (haarColumnSphere hM j)
        (unitaryHaarProbabilityMeasure M)) := by
    rw [hmap]
    exact integrable_complexRankOneProjection_entry hM i₁ i₂
  exact (integrable_map_measure hgmap.aestronglyMeasurable
    (measurable_haarColumnSphere hM j).aemeasurable).mp hgmap

theorem integral_haarColumn_projective_entry
    {M : ℕ} (hM : 1 ≤ M) (j i₁ i₂ : Fin M) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      complexRankOneProjection (haarColumnSphere hM j U) i₁ i₂
        ∂(unitaryHaarProbabilityMeasure M)) =
      (((M : ℝ)⁻¹ : ℝ) : ℂ) * (if i₁ = i₂ then 1 else 0) := by
  let g : ComplexUnitSphere M → ℂ := fun v ↦
    complexRankOneProjection v i₁ i₂
  have hmap := map_haarColumnSphere_unitaryHaarProbabilityMeasure hM j
  have hg : AEStronglyMeasurable g
      (Measure.map (haarColumnSphere hM j)
        (unitaryHaarProbabilityMeasure M)) := by
    rw [hmap]
    exact (integrable_complexRankOneProjection_entry
      hM i₁ i₂).aestronglyMeasurable
  calc
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      complexRankOneProjection (haarColumnSphere hM j U) i₁ i₂
        ∂(unitaryHaarProbabilityMeasure M)) =
      ∫ v, g v ∂Measure.map (haarColumnSphere hM j)
        (unitaryHaarProbabilityMeasure M) := by
          exact (integral_map
            (measurable_haarColumnSphere hM j).aemeasurable hg).symm
    _ = ∫ v, g v ∂complexUnitSphereProbabilityMeasure M := by rw [hmap]
    _ = _ := integral_complexRankOneProjection_entry hM i₁ i₂

theorem integrable_haarColumn_projective_entry_mul
    {M : ℕ} (hM : 1 ≤ M) (j i₁ i₂ i₃ i₄ : Fin M) :
    Integrable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        complexRankOneProjection (haarColumnSphere hM j U) i₁ i₂ *
          complexRankOneProjection (haarColumnSphere hM j U) i₃ i₄)
      (unitaryHaarProbabilityMeasure M) := by
  let g : ComplexUnitSphere M → ℂ := fun v ↦
    complexRankOneProjection v i₁ i₂ * complexRankOneProjection v i₃ i₄
  have hmap := map_haarColumnSphere_unitaryHaarProbabilityMeasure hM j
  have hgmap : Integrable g
      (Measure.map (haarColumnSphere hM j)
        (unitaryHaarProbabilityMeasure M)) := by
    rw [hmap]
    exact integrable_complexRankOneProjection_entry_mul hM i₁ i₂ i₃ i₄
  exact (integrable_map_measure hgmap.aestronglyMeasurable
    (measurable_haarColumnSphere hM j).aemeasurable).mp hgmap

theorem integral_haarColumn_projective_entry_mul
    {M : ℕ} (hM : 1 ≤ M) (j i₁ i₂ i₃ i₄ : Fin M) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      complexRankOneProjection (haarColumnSphere hM j U) i₁ i₂ *
        complexRankOneProjection (haarColumnSphere hM j U) i₃ i₄
        ∂(unitaryHaarProbabilityMeasure M)) =
      ((((M : ℝ) * ((M : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        ((if i₁ = i₂ then 1 else 0) * (if i₃ = i₄ then 1 else 0) +
          (if i₁ = i₄ then 1 else 0) * (if i₃ = i₂ then 1 else 0)) := by
  let g : ComplexUnitSphere M → ℂ := fun v ↦
    complexRankOneProjection v i₁ i₂ * complexRankOneProjection v i₃ i₄
  have hmap := map_haarColumnSphere_unitaryHaarProbabilityMeasure hM j
  have hg : AEStronglyMeasurable g
      (Measure.map (haarColumnSphere hM j)
        (unitaryHaarProbabilityMeasure M)) := by
    rw [hmap]
    exact (integrable_complexRankOneProjection_entry_mul
      hM i₁ i₂ i₃ i₄).aestronglyMeasurable
  calc
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      complexRankOneProjection (haarColumnSphere hM j U) i₁ i₂ *
        complexRankOneProjection (haarColumnSphere hM j U) i₃ i₄
        ∂(unitaryHaarProbabilityMeasure M)) =
      ∫ v, g v ∂Measure.map (haarColumnSphere hM j)
        (unitaryHaarProbabilityMeasure M) := by
          exact (integral_map
            (measurable_haarColumnSphere hM j).aemeasurable hg).symm
    _ = ∫ v, g v ∂complexUnitSphereProbabilityMeasure M := by rw [hmap]
    _ = _ := integral_complexRankOneProjection_entry_mul hM i₁ i₂ i₃ i₄

/-! ## The random prefix projection -/

/-- The first `K` columns of a Haar unitary, retaining all ambient rows. -/
def haarFullRowsTopColumns {M K : ℕ} (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : Matrix (Fin M) (Fin K) ℂ :=
  topLeftUnitaryBlock (le_refl M) hKM U

/-- The rank-`K` orthogonal projection generated by the first `K` columns. -/
def haarPrefixProjection {M K : ℕ} (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  haarFullRowsTopColumns hKM U * (haarFullRowsTopColumns hKM U).conjTranspose

theorem haarFullRowsTopColumns_conjTranspose_mul_self
    {M K : ℕ} (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    (haarFullRowsTopColumns hKM U).conjTranspose *
        haarFullRowsTopColumns hKM U = 1 := by
  have hunit := Matrix.UnitaryGroup.star_mul_self U
  ext i j
  have hij := congrArg
    (fun A : Matrix (Fin M) (Fin M) ℂ ↦
      A (Fin.castLE hKM i) (Fin.castLE hKM j)) hunit
  simpa [haarFullRowsTopColumns, topLeftUnitaryBlock,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.star_eq_conjTranspose, Matrix.one_apply] using hij

theorem haarPrefixProjection_mul_self
    {M K : ℕ} (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    haarPrefixProjection hKM U * haarPrefixProjection hKM U =
      haarPrefixProjection hKM U := by
  unfold haarPrefixProjection
  calc
    (haarFullRowsTopColumns hKM U *
          (haarFullRowsTopColumns hKM U).conjTranspose) *
        (haarFullRowsTopColumns hKM U *
          (haarFullRowsTopColumns hKM U).conjTranspose) =
      haarFullRowsTopColumns hKM U *
        ((haarFullRowsTopColumns hKM U).conjTranspose *
          haarFullRowsTopColumns hKM U) *
        (haarFullRowsTopColumns hKM U).conjTranspose := by
          simp only [Matrix.mul_assoc]
    _ = haarFullRowsTopColumns hKM U *
        (haarFullRowsTopColumns hKM U).conjTranspose := by
      rw [haarFullRowsTopColumns_conjTranspose_mul_self hKM U]
      simp

@[simp]
theorem haarPrefixProjection_apply
    {M K : ℕ} (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) (i j : Fin M) :
    haarPrefixProjection hKM U i j =
      ∑ c : Fin K,
        (U : Matrix (Fin M) (Fin M) ℂ) i (Fin.castLE hKM c) *
          star ((U : Matrix (Fin M) (Fin M) ℂ) j (Fin.castLE hKM c)) := by
  simp [haarPrefixProjection, haarFullRowsTopColumns,
    topLeftUnitaryBlock, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem measurable_haarPrefixProjection_entry
    {M K : ℕ} (hKM : K ≤ M) (i j : Fin M) :
    Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        haarPrefixProjection hKM U i j) := by
  simp_rw [haarPrefixProjection_apply]
  refine Finset.measurable_sum _ fun c _ ↦ ?_
  have hcoe : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        (U : Matrix (Fin M) (Fin M) ℂ)) :=
    measurable_subtype_coe
  have hi : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        (U : Matrix (Fin M) (Fin M) ℂ) i (Fin.castLE hKM c)) :=
    (measurable_pi_apply (Fin.castLE hKM c)).comp
      ((measurable_pi_apply i).comp hcoe)
  have hj : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        (U : Matrix (Fin M) (Fin M) ℂ) j (Fin.castLE hKM c)) :=
    (measurable_pi_apply (Fin.castLE hKM c)).comp
      ((measurable_pi_apply j).comp hcoe)
  exact hi.mul (Complex.continuous_conj.measurable.comp hj)

theorem norm_haarPrefixProjection_entry_le
    {M K : ℕ} (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) (i j : Fin M) :
    ‖haarPrefixProjection hKM U i j‖ ≤ (K : ℝ) := by
  rw [haarPrefixProjection_apply]
  calc
    ‖∑ c : Fin K,
        (U : Matrix (Fin M) (Fin M) ℂ) i (Fin.castLE hKM c) *
          star ((U : Matrix (Fin M) (Fin M) ℂ) j (Fin.castLE hKM c))‖ ≤
      ∑ c : Fin K,
        ‖(U : Matrix (Fin M) (Fin M) ℂ) i (Fin.castLE hKM c) *
          star ((U : Matrix (Fin M) (Fin M) ℂ) j (Fin.castLE hKM c))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _c : Fin K, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro c _
      rw [norm_mul, norm_star]
      exact mul_le_one₀
        (entry_norm_bound_of_unitary U.property i (Fin.castLE hKM c))
        (norm_nonneg _)
        (entry_norm_bound_of_unitary U.property j (Fin.castLE hKM c))
    _ = (K : ℝ) := by simp

theorem integrable_haarPrefixProjection_entry_mul_reverse
    {M K : ℕ} (hKM : K ≤ M) (i j : Fin M) :
    Integrable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        haarPrefixProjection hKM U i j * haarPrefixProjection hKM U j i)
      (unitaryHaarProbabilityMeasure M) := by
  refine (integrable_const ((K : ℝ) ^ 2)).mono
    ((measurable_haarPrefixProjection_entry hKM i j).mul
      (measurable_haarPrefixProjection_entry hKM j i)).aestronglyMeasurable ?_
  filter_upwards [] with U
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (K : ℝ))]
  calc
    ‖haarPrefixProjection hKM U i j‖ *
        ‖haarPrefixProjection hKM U j i‖ ≤ (K : ℝ) * K :=
      mul_le_mul (norm_haarPrefixProjection_entry_le hKM U i j)
        (norm_haarPrefixProjection_entry_le hKM U j i)
        (norm_nonneg _) (Nat.cast_nonneg K)
    _ = (K : ℝ) ^ 2 := by ring

/-! ## Row-permutation covariance -/

/-- A finite permutation matrix as an ambient unitary. -/
def haarPermutationUnitary {M : ℕ} (σ : Equiv.Perm (Fin M)) :
    Matrix.unitaryGroup (Fin M) ℂ := by
  refine ⟨σ.permMatrix ℂ, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp

theorem measurable_unitary_mul_left_h19Gram {M : ℕ}
    (V : Matrix.unitaryGroup (Fin M) ℂ) :
    Measurable (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦ V * U) := by
  apply Measurable.subtype_mk
  change Measurable
    (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
      (V : Matrix (Fin M) (Fin M) ℂ) *
        (U : Matrix (Fin M) (Fin M) ℂ))
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ ↦ ?_
  have hcoe : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        (U : Matrix (Fin M) (Fin M) ℂ)) :=
    measurable_subtype_coe
  exact measurable_const.mul ((measurable_pi_apply j).comp
    ((measurable_pi_apply k).comp hcoe))

@[simp]
theorem haarPermutationUnitary_mul_apply
    {M : ℕ} (σ : Equiv.Perm (Fin M))
    (U : Matrix.unitaryGroup (Fin M) ℂ) (i j : Fin M) :
    ((haarPermutationUnitary σ * U : Matrix.unitaryGroup (Fin M) ℂ) :
        Matrix (Fin M) (Fin M) ℂ) i j =
      (U : Matrix (Fin M) (Fin M) ℂ) (σ i) j := by
  have hvec := Matrix.permMatrix_mulVec
    (R := ℂ) (σ := σ)
    (v := fun k : Fin M ↦ (U : Matrix (Fin M) (Fin M) ℂ) k j)
  have happ := congrFun hvec i
  change
    (σ.permMatrix ℂ *ᵥ
      (fun k : Fin M ↦ (U : Matrix (Fin M) (Fin M) ℂ) k j)) i = _
  simpa using happ

theorem haarPrefixProjection_permutation_mul
    {M K : ℕ} (hKM : K ≤ M) (σ : Equiv.Perm (Fin M))
    (U : Matrix.unitaryGroup (Fin M) ℂ) (i j : Fin M) :
    haarPrefixProjection hKM (haarPermutationUnitary σ * U) i j =
      haarPrefixProjection hKM U (σ i) (σ j) := by
  simp only [haarPrefixProjection_apply, haarPermutationUnitary_mul_apply]

theorem integral_haarPrefixProjection_entry_mul_reverse_permutation
    {M K : ℕ} (hKM : K ≤ M) (σ : Equiv.Perm (Fin M))
    (i j : Fin M) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i j * haarPrefixProjection hKM U j i
        ∂(unitaryHaarProbabilityMeasure M)) =
    ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U (σ i) (σ j) *
        haarPrefixProjection hKM U (σ j) (σ i)
        ∂(unitaryHaarProbabilityMeasure M) := by
  let μ := unitaryHaarProbabilityMeasure M
  let P := haarPermutationUnitary σ
  let F : Matrix.unitaryGroup (Fin M) ℂ → ℂ := fun U ↦
    haarPrefixProjection hKM U i j * haarPrefixProjection hKM U j i
  have hFmeas : AEStronglyMeasurable F (Measure.map (fun U ↦ P * U) μ) :=
    ((measurable_haarPrefixProjection_entry hKM i j).mul
      (measurable_haarPrefixProjection_entry hKM j i)).aestronglyMeasurable
  letI : IsProbabilityMeasure μ :=
    unitaryHaarProbabilityMeasure_isProbability M
  letI : Measure.IsHaarMeasure μ :=
    canonicalUnitaryHaarProbabilityFamily.isHaar M
  calc
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i j * haarPrefixProjection hKM U j i
        ∂(unitaryHaarProbabilityMeasure M)) =
      ∫ U, F U ∂Measure.map (fun U ↦ P * U) μ := by
        rw [map_mul_left_eq_self μ P]
    _ = ∫ U, F (P * U) ∂μ :=
      integral_map (measurable_unitary_mul_left_h19Gram P).aemeasurable hFmeas
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with U
      simp only [F, P]
      rw [haarPrefixProjection_permutation_mul,
        haarPrefixProjection_permutation_mul]

theorem integral_haarPrefixProjection_entry_mul_reverse_eq_of_offdiag
    {M K : ℕ} (hKM : K ≤ M) (i j l : Fin M)
    (hij : i ≠ j) (hil : i ≠ l) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i j * haarPrefixProjection hKM U j i
        ∂(unitaryHaarProbabilityMeasure M)) =
    ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i l * haarPrefixProjection hKM U l i
        ∂(unitaryHaarProbabilityMeasure M) := by
  have h := integral_haarPrefixProjection_entry_mul_reverse_permutation
    hKM (Equiv.swap j l) i j
  simpa only [Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hij hil] using h

theorem sum_haarPrefixProjection_entry_mul_reverse
    {M K : ℕ} (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) (i : Fin M) :
    ∑ j : Fin M,
      haarPrefixProjection hKM U i j * haarPrefixProjection hKM U j i =
        haarPrefixProjection hKM U i i := by
  have h := congrArg
    (fun A : Matrix (Fin M) (Fin M) ℂ ↦ A i i)
    (haarPrefixProjection_mul_self hKM U)
  simpa only [Matrix.mul_apply] using h

theorem haarPrefixProjection_conj_symm
    {M K : ℕ} (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) (i j : Fin M) :
    star (haarPrefixProjection hKM U i j) =
      haarPrefixProjection hKM U j i := by
  have hHerm : (haarPrefixProjection hKM U).conjTranspose =
      haarPrefixProjection hKM U := by
    unfold haarPrefixProjection
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hij := congrArg
    (fun A : Matrix (Fin M) (Fin M) ℂ ↦ A j i) hHerm
  simpa [Matrix.conjTranspose_apply] using hij

/-! ## Diagonal second moment -/

theorem haarPrefixProjection_inv_diag_eq_projective_sum
    {M K : ℕ} (hM : 1 ≤ M) (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) (i : Fin M) :
    haarPrefixProjection hKM U⁻¹ i i =
      ∑ c : Fin K,
        complexRankOneProjection (haarColumnSphere hM i U)
          (Fin.castLE hKM c) (Fin.castLE hKM c) := by
  rw [haarPrefixProjection_apply]
  apply Finset.sum_congr rfl
  intro c _
  unfold complexRankOneProjection
  rw [haarColumnSphere_apply]
  simp [mul_comm]

/-- The exact diagonal first moment of the random rank-`K` projection. -/
theorem integral_haarPrefixProjection_diag
    {M K : ℕ} (hM : 1 ≤ M) (hKM : K ≤ M) (i : Fin M) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i i
        ∂(unitaryHaarProbabilityMeasure M)) =
      (((M : ℝ)⁻¹ : ℝ) : ℂ) * (K : ℂ) := by
  let μ := unitaryHaarProbabilityMeasure M
  let F : Matrix.unitaryGroup (Fin M) ℂ → ℂ := fun U ↦
    haarPrefixProjection hKM U i i
  have hFmeas : AEStronglyMeasurable F (Measure.map Inv.inv μ) :=
    (measurable_haarPrefixProjection_entry hKM i i).aestronglyMeasurable
  calc
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i i
        ∂(unitaryHaarProbabilityMeasure M)) =
      ∫ U, F U ∂Measure.map Inv.inv μ := by
        rw [map_unitaryHaarProbabilityMeasure_inv_H19]
    _ = ∫ U, F U⁻¹ ∂μ :=
      integral_map (measurable_unitary_inv_h19Gram M).aemeasurable hFmeas
    _ = ∫ U, ∑ c : Fin K,
        complexRankOneProjection (haarColumnSphere hM i U)
          (Fin.castLE hKM c) (Fin.castLE hKM c) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with U
      exact haarPrefixProjection_inv_diag_eq_projective_sum hM hKM U i
    _ = ∑ c : Fin K, ∫ U,
        complexRankOneProjection (haarColumnSphere hM i U)
          (Fin.castLE hKM c) (Fin.castLE hKM c) ∂μ := by
      rw [integral_finset_sum]
      intro c _
      exact integrable_haarColumn_projective_entry hM i
        (Fin.castLE hKM c) (Fin.castLE hKM c)
    _ = (((M : ℝ)⁻¹ : ℝ) : ℂ) * (K : ℂ) := by
      calc
        _ = ∑ _c : Fin K, (((M : ℝ)⁻¹ : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro c _
          rw [integral_haarColumn_projective_entry hM]
          simp
        _ = _ := by simp [mul_comm]

private theorem sum_fin_pair_one_add_cast_indicator
    {M K : ℕ} (hKM : K ≤ M) :
    (∑ c : Fin K, ∑ d : Fin K,
      ((1 : ℂ) +
        (if Fin.castLE hKM c = Fin.castLE hKM d then 1 else 0))) =
      (K : ℂ) * ((K : ℂ) + 1) := by
  calc
    _ = ∑ _c : Fin K, ((K : ℂ) + 1) := by
      apply Finset.sum_congr rfl
      intro c _
      simp_rw [Fin.castLE_inj]
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by
      simp
      ring

/-- The exact diagonal second moment of the random rank-`K` projection. -/
theorem integral_haarPrefixProjection_diag_sq
    {M K : ℕ} (hM : 1 ≤ M) (hKM : K ≤ M) (i : Fin M) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i i * haarPrefixProjection hKM U i i
        ∂(unitaryHaarProbabilityMeasure M)) =
      ((((M : ℝ) * ((M : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        ((K : ℂ) * ((K : ℂ) + 1)) := by
  let μ := unitaryHaarProbabilityMeasure M
  let F : Matrix.unitaryGroup (Fin M) ℂ → ℂ := fun U ↦
    haarPrefixProjection hKM U i i * haarPrefixProjection hKM U i i
  have hFmeas : AEStronglyMeasurable F (Measure.map Inv.inv μ) := by
    exact ((measurable_haarPrefixProjection_entry hKM i i).mul
      (measurable_haarPrefixProjection_entry hKM i i)).aestronglyMeasurable
  calc
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i i * haarPrefixProjection hKM U i i
        ∂(unitaryHaarProbabilityMeasure M)) =
      ∫ U, F U ∂Measure.map Inv.inv μ := by
        rw [map_unitaryHaarProbabilityMeasure_inv_H19]
    _ = ∫ U, F U⁻¹ ∂μ :=
      integral_map (measurable_unitary_inv_h19Gram M).aemeasurable hFmeas
    _ = ∫ U, (∑ c : Fin K,
          complexRankOneProjection (haarColumnSphere hM i U)
            (Fin.castLE hKM c) (Fin.castLE hKM c)) *
        (∑ d : Fin K,
          complexRankOneProjection (haarColumnSphere hM i U)
            (Fin.castLE hKM d) (Fin.castLE hKM d)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with U
      simp only [F]
      rw [haarPrefixProjection_inv_diag_eq_projective_sum hM hKM]
    _ = ∫ U, ∑ c : Fin K, ∑ d : Fin K,
        complexRankOneProjection (haarColumnSphere hM i U)
            (Fin.castLE hKM c) (Fin.castLE hKM c) *
          complexRankOneProjection (haarColumnSphere hM i U)
            (Fin.castLE hKM d) (Fin.castLE hKM d) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with U
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
    _ = ∑ c : Fin K, ∑ d : Fin K,
        ∫ U,
          complexRankOneProjection (haarColumnSphere hM i U)
              (Fin.castLE hKM c) (Fin.castLE hKM c) *
            complexRankOneProjection (haarColumnSphere hM i U)
              (Fin.castLE hKM d) (Fin.castLE hKM d) ∂μ := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro c _
        rw [integral_finset_sum]
        intro d _
        exact integrable_haarColumn_projective_entry_mul hM i
          (Fin.castLE hKM c) (Fin.castLE hKM c)
          (Fin.castLE hKM d) (Fin.castLE hKM d)
      · intro c _
        exact integrable_finset_sum _ fun d _ ↦
          integrable_haarColumn_projective_entry_mul hM i
            (Fin.castLE hKM c) (Fin.castLE hKM c)
            (Fin.castLE hKM d) (Fin.castLE hKM d)
    _ = ((((M : ℝ) * ((M : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        ((K : ℂ) * ((K : ℂ) + 1)) := by
      apply Eq.trans ?_ (congrArg
        (fun z : ℂ ↦
          ((((M : ℝ) * ((M : ℝ) + 1))⁻¹ : ℝ) : ℂ) * z)
        (sum_fin_pair_one_add_cast_indicator hKM))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [integral_haarColumn_projective_entry_mul hM]
      by_cases hcd : c = d
      · subst d
        simp
      · have hcast : Fin.castLE hKM c ≠ Fin.castLE hKM d := by
          exact fun h ↦ hcd (Fin.castLE_injective hKM h)
        simp [hcast, hcast.symm]

/-! ## Off-diagonal second moment -/

/-- The off-diagonal projection moment, first in the subtraction/division
form obtained directly from `Q² = Q`. -/
theorem integral_haarPrefixProjection_offdiag_eq_difference_div
    {M K : ℕ} (hM2 : 2 ≤ M) (hKM : K ≤ M) (i j : Fin M)
    (hij : i ≠ j) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i j * haarPrefixProjection hKM U j i
        ∂(unitaryHaarProbabilityMeasure M)) =
      (((((M : ℝ)⁻¹ : ℝ) : ℂ) * (K : ℂ)) -
        (((((M : ℝ) * ((M : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          ((K : ℂ) * ((K : ℂ) + 1)))) /
        (((M - 1 : ℕ) : ℕ) : ℂ) := by
  have hM : 1 ≤ M := by omega
  let μ := unitaryHaarProbabilityMeasure M
  let f : Fin M → ℂ := fun l ↦
    ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i l * haarPrefixProjection hKM U l i ∂μ
  have hsum :
      (∑ l : Fin M, f l) = (((M : ℝ)⁻¹ : ℝ) : ℂ) * (K : ℂ) := by
    calc
      (∑ l : Fin M, f l) =
          ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
            ∑ l : Fin M,
              haarPrefixProjection hKM U i l *
                haarPrefixProjection hKM U l i ∂μ := by
        symm
        rw [integral_finset_sum]
        intro l _
        exact integrable_haarPrefixProjection_entry_mul_reverse hKM i l
      _ = ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
          haarPrefixProjection hKM U i i ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with U
        exact sum_haarPrefixProjection_entry_mul_reverse hKM U i
      _ = (((M : ℝ)⁻¹ : ℝ) : ℂ) * (K : ℂ) :=
        integral_haarPrefixProjection_diag hM hKM i
  have hconst : ∀ l ∈ (Finset.univ : Finset (Fin M)).erase i,
      f l = f j := by
    intro l hl
    have hil : i ≠ l := by
      exact Ne.symm (Finset.ne_of_mem_erase hl)
    exact (integral_haarPrefixProjection_entry_mul_reverse_eq_of_offdiag
      hKM i j l hij hil).symm
  have hsplit :
      (∑ l : Fin M, f l) =
        (((M - 1 : ℕ) : ℕ) : ℂ) * f j + f i := by
    calc
      (∑ l : Fin M, f l) =
          (∑ l ∈ (Finset.univ : Finset (Fin M)).erase i, f l) + f i := by
        simpa using (Finset.sum_erase_add (Finset.univ : Finset (Fin M))
          f (Finset.mem_univ i)).symm
      _ = ((Finset.univ : Finset (Fin M)).erase i).card • f j + f i := by
        rw [Finset.sum_eq_card_nsmul hconst]
      _ = (((M - 1 : ℕ) : ℕ) : ℂ) * f j + f i := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp [nsmul_eq_mul]
  have heq :
      (((M - 1 : ℕ) : ℕ) : ℂ) * f j +
          ((((M : ℝ) * ((M : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
            ((K : ℂ) * ((K : ℂ) + 1)) =
        (((M : ℝ)⁻¹ : ℝ) : ℂ) * (K : ℂ) := by
    calc
      (((M - 1 : ℕ) : ℕ) : ℂ) * f j +
          ((((M : ℝ) * ((M : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
            ((K : ℂ) * ((K : ℂ) + 1)) =
        (((M - 1 : ℕ) : ℕ) : ℂ) * f j + f i := by
          change _ = _ +
            (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
              haarPrefixProjection hKM U i i *
                haarPrefixProjection hKM U i i
                ∂(unitaryHaarProbabilityMeasure M))
          rw [integral_haarPrefixProjection_diag_sq hM hKM i]
      _ = ∑ l : Fin M, f l := hsplit.symm
      _ = (((M : ℝ)⁻¹ : ℝ) : ℂ) * (K : ℂ) := hsum
  have hden : (((M - 1 : ℕ) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt (by omega : 1 < M)))
  change f j = _
  apply (eq_div_iff hden).2
  linear_combination heq

/-- The off-diagonal projection moment in its closed rational form. -/
theorem integral_haarPrefixProjection_offdiag
    {M K : ℕ} (hM2 : 2 ≤ M) (hKM : K ≤ M) (i j : Fin M)
    (hij : i ≠ j) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarPrefixProjection hKM U i j * haarPrefixProjection hKM U j i
        ∂(unitaryHaarProbabilityMeasure M)) =
      (((K : ℝ) * ((M : ℝ) - K) /
        ((M : ℝ) * ((M : ℝ) ^ 2 - 1)) : ℝ) : ℂ) := by
  rw [integral_haarPrefixProjection_offdiag_eq_difference_div
    hM2 hKM i j hij]
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hMone : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (show 1 < M by omega)
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hMm1 : (M : ℝ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hMone)
  have hMp1 : (M : ℝ) + 1 ≠ 0 := by positivity
  have hMsq1 : (M : ℝ) ^ 2 - 1 ≠ 0 := by
    rw [show (M : ℝ) ^ 2 - 1 =
      ((M : ℝ) - 1) * ((M : ℝ) + 1) by ring]
    exact mul_ne_zero hMm1 hMp1
  have hcastSub : (((M - 1 : ℕ) : ℕ) : ℂ) = ((M : ℝ) - 1 : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  rw [hcastSub]
  have hreal :
      (((M : ℝ)⁻¹ * (K : ℝ) -
          ((M : ℝ) * ((M : ℝ) + 1))⁻¹ *
            ((K : ℝ) * ((K : ℝ) + 1))) /
        ((M : ℝ) - 1)) =
      (K : ℝ) * ((M : ℝ) - K) /
        ((M : ℝ) * ((M : ℝ) ^ 2 - 1)) := by
    field_simp [hM0, hMm1, hMp1, hMsq1]
    ring
  simpa only [Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) hreal

/-! ## Scaled block energies -/

/-- The row Gram matrix of the scaled upper-left block is the corresponding
principal submatrix of `M` times the random prefix projection. -/
theorem sqrtScaledHaarBlockMatrix_mul_conjTranspose_apply
    {M N K : ℕ} (hNM : N ≤ M) (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) (i j : Fin N) :
    (sqrtScaledHaarBlockMatrix hNM hKM U *
        (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose) i j =
      (M : ℂ) * haarPrefixProjection hKM U
        (Fin.castLE hNM i) (Fin.castLE hNM j) := by
  have hsqrt : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg M)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    sqrtScaledHaarBlockMatrix, haarPrefixProjection_apply,
    topLeftUnitaryBlock]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [star_mul, Complex.star_def, Complex.conj_ofReal]
  have hsqrtC :
      ((Real.sqrt (M : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt (M : ℝ) : ℝ) : ℂ) = (M : ℂ) := by
    exact_mod_cast hsqrt
  calc
    ((Real.sqrt (M : ℝ) : ℝ) : ℂ) *
          (U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hNM i)
            (Fin.castLE hKM c) *
        ((starRingEnd ℂ)
            ((U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hNM j)
              (Fin.castLE hKM c)) *
          ((Real.sqrt (M : ℝ) : ℝ) : ℂ)) =
        (((Real.sqrt (M : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt (M : ℝ) : ℝ) : ℂ)) *
          ((U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hNM i)
              (Fin.castLE hKM c) *
            (starRingEnd ℂ)
              ((U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hNM j)
                (Fin.castLE hKM c))) := by ring
    _ = _ := by rw [hsqrtC]

theorem integrable_haarPrefixProjection_entry
    {M K : ℕ} (hKM : K ≤ M) (i j : Fin M) :
    Integrable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        haarPrefixProjection hKM U i j)
      (unitaryHaarProbabilityMeasure M) := by
  refine (integrable_const (K : ℝ)).mono
    (measurable_haarPrefixProjection_entry hKM i j).aestronglyMeasurable ?_
  filter_upwards [] with U
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (K : ℝ))] using
    norm_haarPrefixProjection_entry_le hKM U i j

theorem trace_sqrtScaledHaarBlock_rowGram
    {M N K : ℕ} (hNM : N ≤ M) (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Matrix.trace
        (sqrtScaledHaarBlockMatrix hNM hKM U *
          (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose) =
      (M : ℂ) * ∑ i : Fin N,
        haarPrefixProjection hKM U (Fin.castLE hNM i) (Fin.castLE hNM i) := by
  rw [Matrix.trace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact sqrtScaledHaarBlockMatrix_mul_conjTranspose_apply hNM hKM U i i

theorem trace_sq_sqrtScaledHaarBlock_rowGram
    {M N K : ℕ} (hNM : N ≤ M) (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Matrix.trace
        ((sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose) *
          (sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose)) =
      (M : ℂ) ^ 2 * ∑ i : Fin N, ∑ j : Fin N,
        haarPrefixProjection hKM U (Fin.castLE hNM i) (Fin.castLE hNM j) *
          haarPrefixProjection hKM U (Fin.castLE hNM j) (Fin.castLE hNM i) := by
  rw [Matrix.trace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply]
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [sqrtScaledHaarBlockMatrix_mul_conjTranspose_apply hNM hKM,
    sqrtScaledHaarBlockMatrix_mul_conjTranspose_apply hNM hKM]
  ring

theorem integrable_trace_sqrtScaledHaarBlock_rowGram
    {M N K : ℕ} (hNM : N ≤ M) (hKM : K ≤ M) :
    Integrable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        Matrix.trace
          (sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose))
      (unitaryHaarProbabilityMeasure M) := by
  have hsum : Integrable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        ∑ i : Fin N,
          haarPrefixProjection hKM U
            (Fin.castLE hNM i) (Fin.castLE hNM i))
      (unitaryHaarProbabilityMeasure M) :=
    integrable_finset_sum _ fun i _ ↦
      integrable_haarPrefixProjection_entry hKM
        (Fin.castLE hNM i) (Fin.castLE hNM i)
  exact (hsum.const_mul (M : ℂ)).congr
    (ae_of_all _ fun U ↦ (trace_sqrtScaledHaarBlock_rowGram hNM hKM U).symm)

theorem integral_trace_sqrtScaledHaarBlock_rowGram
    {M N K : ℕ} (hM : 1 ≤ M) (hNM : N ≤ M) (hKM : K ≤ M) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      Matrix.trace
        (sqrtScaledHaarBlockMatrix hNM hKM U *
          (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose)
        ∂(unitaryHaarProbabilityMeasure M)) =
      (N : ℂ) * (K : ℂ) := by
  simp_rw [trace_sqrtScaledHaarBlock_rowGram hNM hKM]
  rw [integral_const_mul, integral_finset_sum]
  · calc
      (M : ℂ) *
          ∑ i : Fin N,
            ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
              haarPrefixProjection hKM U
                (Fin.castLE hNM i) (Fin.castLE hNM i)
                ∂(unitaryHaarProbabilityMeasure M) =
        (M : ℂ) * ∑ _i : Fin N,
          ((((M : ℝ)⁻¹ : ℝ) : ℂ) * (K : ℂ)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [integral_haarPrefixProjection_diag hM hKM]
      _ = (N : ℂ) * (K : ℂ) := by
        have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        norm_cast
        field_simp
        norm_cast
  · intro i _
    exact integrable_haarPrefixProjection_entry hKM
      (Fin.castLE hNM i) (Fin.castLE hNM i)

private theorem sum_fin_pair_diag_offdiag_complex
    {N : ℕ} (hN : 1 ≤ N) (D O : ℂ) :
    (∑ i : Fin N, ∑ j : Fin N, if i = j then D else O) =
      (N : ℂ) * D + ((N * (N - 1) : ℕ) : ℂ) * O := by
  have hinner : ∀ i : Fin N,
      (∑ j : Fin N, if i = j then D else O) =
        D + ((N - 1 : ℕ) : ℂ) * O := by
    intro i
    calc
      (∑ j : Fin N, if i = j then D else O) =
          (∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
            if i = j then D else O) + (if i = i then D else O) := by
        simpa using (Finset.sum_erase_add (Finset.univ : Finset (Fin N))
          (fun j : Fin N ↦ if i = j then D else O)
          (Finset.mem_univ i)).symm
      _ = ((Finset.univ : Finset (Fin N)).erase i).card • O + D := by
        have hconst : ∀ j ∈ (Finset.univ : Finset (Fin N)).erase i,
            (if i = j then D else O) = O := by
          intro j hj
          have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
          simp [hij]
        rw [Finset.sum_eq_card_nsmul hconst]
        simp
      _ = D + ((N - 1 : ℕ) : ℂ) * O := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp [nsmul_eq_mul]
        ring
  calc
    (∑ i : Fin N, ∑ j : Fin N, if i = j then D else O) =
        ∑ _i : Fin N, (D + ((N - 1 : ℕ) : ℂ) * O) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hinner i
    _ = (N : ℂ) * D + ((N * (N - 1) : ℕ) : ℂ) * O := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

theorem integrable_trace_sq_sqrtScaledHaarBlock_rowGram
    {M N K : ℕ} (hNM : N ≤ M) (hKM : K ≤ M) :
    Integrable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        Matrix.trace
          ((sqrtScaledHaarBlockMatrix hNM hKM U *
              (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose) *
            (sqrtScaledHaarBlockMatrix hNM hKM U *
              (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose)))
      (unitaryHaarProbabilityMeasure M) := by
  have hsum : Integrable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        ∑ i : Fin N, ∑ j : Fin N,
          haarPrefixProjection hKM U
              (Fin.castLE hNM i) (Fin.castLE hNM j) *
            haarPrefixProjection hKM U
              (Fin.castLE hNM j) (Fin.castLE hNM i))
      (unitaryHaarProbabilityMeasure M) :=
    integrable_finset_sum _ fun i _ ↦
      integrable_finset_sum _ fun j _ ↦
        integrable_haarPrefixProjection_entry_mul_reverse hKM
          (Fin.castLE hNM i) (Fin.castLE hNM j)
  exact (hsum.const_mul ((M : ℂ) ^ 2)).congr
    (ae_of_all _ fun U ↦
      (trace_sq_sqrtScaledHaarBlock_rowGram hNM hKM U).symm)

/-- Exact scaled row-Gram second moment, with the diagonal and off-diagonal
contributions displayed separately. -/
theorem integral_trace_sq_sqrtScaledHaarBlock_rowGram_pairForm
    {M N K : ℕ} (hM2 : 2 ≤ M) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hKM : K ≤ M) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      Matrix.trace
        ((sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose) *
          (sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose))
        ∂(unitaryHaarProbabilityMeasure M)) =
      (M : ℂ) ^ 2 *
        ((N : ℂ) *
            (((((M : ℝ) * ((M : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
              ((K : ℂ) * ((K : ℂ) + 1))) +
          ((N * (N - 1) : ℕ) : ℂ) *
            (((K : ℝ) * ((M : ℝ) - K) /
              ((M : ℝ) * ((M : ℝ) ^ 2 - 1)) : ℝ) : ℂ)) := by
  simp_rw [trace_sq_sqrtScaledHaarBlock_rowGram hNM hKM]
  rw [integral_const_mul]
  rw [integral_finset_sum]
  · congr 1
    rw [show
      (∑ i : Fin N,
        ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
          ∑ j : Fin N,
            haarPrefixProjection hKM U
                (Fin.castLE hNM i) (Fin.castLE hNM j) *
              haarPrefixProjection hKM U
                (Fin.castLE hNM j) (Fin.castLE hNM i)
            ∂(unitaryHaarProbabilityMeasure M)) =
        ∑ i : Fin N, ∑ j : Fin N,
          ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
            haarPrefixProjection hKM U
                (Fin.castLE hNM i) (Fin.castLE hNM j) *
              haarPrefixProjection hKM U
                (Fin.castLE hNM j) (Fin.castLE hNM i)
              ∂(unitaryHaarProbabilityMeasure M) by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finset_sum]
        intro j _
        exact integrable_haarPrefixProjection_entry_mul_reverse hKM
          (Fin.castLE hNM i) (Fin.castLE hNM j)]
    calc
      (∑ i : Fin N, ∑ j : Fin N,
        ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
          haarPrefixProjection hKM U
              (Fin.castLE hNM i) (Fin.castLE hNM j) *
            haarPrefixProjection hKM U
              (Fin.castLE hNM j) (Fin.castLE hNM i)
            ∂(unitaryHaarProbabilityMeasure M)) =
          ∑ i : Fin N, ∑ j : Fin N,
            if i = j then
              (((((M : ℝ) * ((M : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
                ((K : ℂ) * ((K : ℂ) + 1)))
            else
              (((K : ℝ) * ((M : ℝ) - K) /
                ((M : ℝ) * ((M : ℝ) ^ 2 - 1)) : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · subst j
          simp only [ite_true]
          rw [integral_haarPrefixProjection_diag_sq (by omega) hKM]
        · simp only [hij, ite_false]
          have hcast : Fin.castLE hNM i ≠ Fin.castLE hNM j :=
            fun h ↦ hij (Fin.castLE_injective hNM h)
          rw [integral_haarPrefixProjection_offdiag hM2 hKM _ _ hcast]
      _ = _ := sum_fin_pair_diag_offdiag_complex hN _ _
  · intro i _
    exact integrable_finset_sum _ fun j _ ↦
      integrable_haarPrefixProjection_entry_mul_reverse hKM
        (Fin.castLE hNM i) (Fin.castLE hNM j)

/-- Exact scaled row-Gram second moment in the closed form used by the
quantitative likelihood cancellation. -/
theorem integral_trace_sq_sqrtScaledHaarBlock_rowGram
    {M N K : ℕ} (hM2 : 2 ≤ M) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hKM : K ≤ M) :
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      Matrix.trace
        ((sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose) *
          (sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose))
        ∂(unitaryHaarProbabilityMeasure M)) =
      (((N : ℝ) * K * M *
          ((M : ℝ) * ((N : ℝ) + K) - (N : ℝ) * K - 1) /
        ((M : ℝ) ^ 2 - 1) : ℝ) : ℂ) := by
  rw [integral_trace_sq_sqrtScaledHaarBlock_rowGram_pairForm
    hM2 hN hNM hKM]
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hMp1 : (M : ℝ) + 1 ≠ 0 := by positivity
  have hMm1 : (M : ℝ) - 1 ≠ 0 := by
    have hMone : (1 : ℝ) < (M : ℝ) := by
      exact_mod_cast (show 1 < M by omega)
    exact sub_ne_zero.mpr (ne_of_gt hMone)
  have hMsq1 : (M : ℝ) ^ 2 - 1 ≠ 0 := by
    rw [show (M : ℝ) ^ 2 - 1 =
      ((M : ℝ) - 1) * ((M : ℝ) + 1) by ring]
    exact mul_ne_zero hMm1 hMp1
  have hreal :
      (M : ℝ) ^ 2 *
        ((N : ℝ) *
            (((M : ℝ) * ((M : ℝ) + 1))⁻¹ *
              ((K : ℝ) * ((K : ℝ) + 1))) +
          ((N * (N - 1) : ℕ) : ℝ) *
            ((K : ℝ) * ((M : ℝ) - K) /
              ((M : ℝ) * ((M : ℝ) ^ 2 - 1)))) =
      (N : ℝ) * K * M *
          ((M : ℝ) * ((N : ℝ) + K) - (N : ℝ) * K - 1) /
        ((M : ℝ) ^ 2 - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hN]
    field_simp [hM0, hMp1, hMm1, hMsq1]
    ring
  simpa only [Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_ofNat,
    Complex.ofReal_one] using congrArg (fun x : ℝ ↦ (x : ℂ)) hreal

/-! ## Passage to the canonical scaled block law -/

theorem integrable_rowGramEnergy_sqrtScaledHaarBlockLaw_canonical
    {M N K : ℕ} (hNM : N ≤ M) (hKM : K ≤ M) :
    Integrable
      (fun Z : Matrix (Fin N) (Fin K) ℂ ↦
        (Matrix.trace (Z * Z.conjTranspose)).re)
      (sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily M N K) := by
  let g : Matrix (Fin N) (Fin K) ℂ → ℝ := fun Z ↦
    (Matrix.trace (Z * Z.conjTranspose)).re
  have hg : Measurable g := by
    dsimp only [g]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    fun_prop
  rw [sqrtScaledHaarBlockLaw, dif_pos ⟨hNM, hKM⟩]
  rw [normalizedUnitaryHaarLaw_eq_canonical
    canonicalUnitaryHaarProbabilityFamily M]
  apply (integrable_map_measure hg.aestronglyMeasurable
    (measurable_sqrtScaledHaarBlockMatrix hNM hKM).aemeasurable).2
  exact (integrable_trace_sqrtScaledHaarBlock_rowGram hNM hKM).re.congr
    (ae_of_all _ fun _U ↦ rfl)

theorem integral_rowGramEnergy_sqrtScaledHaarBlockLaw_canonical
    {M N K : ℕ} (hM : 1 ≤ M) (hNM : N ≤ M) (hKM : K ≤ M) :
    (∫ Z : Matrix (Fin N) (Fin K) ℂ,
      (Matrix.trace (Z * Z.conjTranspose)).re
        ∂(sqrtScaledHaarBlockLaw
          canonicalUnitaryHaarProbabilityFamily M N K)) =
      (N : ℝ) * (K : ℝ) := by
  let g : Matrix (Fin N) (Fin K) ℂ → ℝ := fun Z ↦
    (Matrix.trace (Z * Z.conjTranspose)).re
  have hg : Measurable g := by
    dsimp only [g]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    fun_prop
  rw [sqrtScaledHaarBlockLaw, dif_pos ⟨hNM, hKM⟩]
  rw [normalizedUnitaryHaarLaw_eq_canonical
    canonicalUnitaryHaarProbabilityFamily M]
  rw [integral_map
    (measurable_sqrtScaledHaarBlockMatrix hNM hKM).aemeasurable
    hg.aestronglyMeasurable]
  change (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      (Matrix.trace
        (sqrtScaledHaarBlockMatrix hNM hKM U *
          (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose)).re
        ∂(unitaryHaarProbabilityMeasure M)) = _
  calc
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
        (Matrix.trace
          (sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose)).re
          ∂(unitaryHaarProbabilityMeasure M)) =
        (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
          Matrix.trace
            (sqrtScaledHaarBlockMatrix hNM hKM U *
              (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose)
            ∂(unitaryHaarProbabilityMeasure M)).re := by
          exact integral_re
            (integrable_trace_sqrtScaledHaarBlock_rowGram hNM hKM)
    _ = (N : ℝ) * (K : ℝ) := by
      rw [integral_trace_sqrtScaledHaarBlock_rowGram hM hNM hKM]
      norm_num

theorem integrable_rowGramSecondEnergy_sqrtScaledHaarBlockLaw_canonical
    {M N K : ℕ} (hNM : N ≤ M) (hKM : K ≤ M) :
    Integrable
      (fun Z : Matrix (Fin N) (Fin K) ℂ ↦
        (Matrix.trace ((Z * Z.conjTranspose) *
          (Z * Z.conjTranspose))).re)
      (sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily M N K) := by
  let g : Matrix (Fin N) (Fin K) ℂ → ℝ := fun Z ↦
    (Matrix.trace ((Z * Z.conjTranspose) *
      (Z * Z.conjTranspose))).re
  have hg : Measurable g := by
    dsimp only [g]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    fun_prop
  rw [sqrtScaledHaarBlockLaw, dif_pos ⟨hNM, hKM⟩]
  rw [normalizedUnitaryHaarLaw_eq_canonical
    canonicalUnitaryHaarProbabilityFamily M]
  apply (integrable_map_measure hg.aestronglyMeasurable
    (measurable_sqrtScaledHaarBlockMatrix hNM hKM).aemeasurable).2
  exact (integrable_trace_sq_sqrtScaledHaarBlock_rowGram hNM hKM).re.congr
    (ae_of_all _ fun _U ↦ rfl)

theorem integral_rowGramSecondEnergy_sqrtScaledHaarBlockLaw_canonical
    {M N K : ℕ} (hM2 : 2 ≤ M) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hKM : K ≤ M) :
    (∫ Z : Matrix (Fin N) (Fin K) ℂ,
      (Matrix.trace ((Z * Z.conjTranspose) *
        (Z * Z.conjTranspose))).re
        ∂(sqrtScaledHaarBlockLaw
          canonicalUnitaryHaarProbabilityFamily M N K)) =
      (N : ℝ) * K * M *
          ((M : ℝ) * ((N : ℝ) + K) - (N : ℝ) * K - 1) /
        ((M : ℝ) ^ 2 - 1) := by
  let g : Matrix (Fin N) (Fin K) ℂ → ℝ := fun Z ↦
    (Matrix.trace ((Z * Z.conjTranspose) *
      (Z * Z.conjTranspose))).re
  have hg : Measurable g := by
    dsimp only [g]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    fun_prop
  rw [sqrtScaledHaarBlockLaw, dif_pos ⟨hNM, hKM⟩]
  rw [normalizedUnitaryHaarLaw_eq_canonical
    canonicalUnitaryHaarProbabilityFamily M]
  rw [integral_map
    (measurable_sqrtScaledHaarBlockMatrix hNM hKM).aemeasurable
    hg.aestronglyMeasurable]
  change (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
      (Matrix.trace
        ((sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose) *
          (sqrtScaledHaarBlockMatrix hNM hKM U *
            (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose))).re
        ∂(unitaryHaarProbabilityMeasure M)) = _
  calc
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
        (Matrix.trace
          ((sqrtScaledHaarBlockMatrix hNM hKM U *
              (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose) *
            (sqrtScaledHaarBlockMatrix hNM hKM U *
              (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose))).re
          ∂(unitaryHaarProbabilityMeasure M)) =
        (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
          Matrix.trace
            ((sqrtScaledHaarBlockMatrix hNM hKM U *
                (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose) *
              (sqrtScaledHaarBlockMatrix hNM hKM U *
                (sqrtScaledHaarBlockMatrix hNM hKM U).conjTranspose))
            ∂(unitaryHaarProbabilityMeasure M)).re := by
          exact integral_re
            (integrable_trace_sq_sqrtScaledHaarBlock_rowGram hNM hKM)
    _ = _ := by
      rw [integral_trace_sq_sqrtScaledHaarBlock_rowGram hM2 hN hNM hKM]
      change
        (((N : ℝ) * K * M *
            ((M : ℝ) * ((N : ℝ) + K) - (N : ℝ) * K - 1) /
          ((M : ℝ) ^ 2 - 1) : ℝ) : ℂ).re = _
      rw [Complex.ofReal_re]

/-! ## Jiang tall-law statements -/

/-- The elementary quadratic energy is integrable under Jiang's scaled tall
corner law. -/
theorem integrable_jiangSqrtScaledTallHaarCorner_energy
    {M K N : ℕ} (hNK : N ≤ K) (hs : K + N ≤ M) :
    Integrable
      (fun Z : Matrix (Fin K) (Fin N) ℂ ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N) := by
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := by omega
  let e := rectangularConjTransposeMeasurableEquiv K N
  let g : Matrix (Fin N) (Fin K) ℂ → ℝ := fun Z ↦
    (Matrix.trace (Z * Z.conjTranspose)).re
  have hg : Measurable g := by
    dsimp only [g]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    fun_prop
  have hwide :=
    integrable_rowGramEnergy_sqrtScaledHaarBlockLaw_canonical hNM hKM
  rw [← map_rectangularConjTranspose_jiangSqrtScaledTallHaarCornerLaw
    hNK hs] at hwide
  have hcomp := (integrable_map_measure hg.aestronglyMeasurable
    e.measurable.aemeasurable).mp hwide
  exact hcomp.congr (ae_of_all _ fun Z ↦ by
    simp only [g, e, Function.comp_apply,
      rectangularConjTransposeMeasurableEquiv_apply,
      Matrix.conjTranspose_conjTranspose])

/-- The exact mean quadratic energy under Jiang's scaled tall law. -/
theorem integral_jiangSqrtScaledTallHaarCorner_energy
    {M K N : ℕ} (hN : 0 < N) (hNK : N ≤ K) (hs : K + N ≤ M) :
    (∫ Z : Matrix (Fin K) (Fin N) ℂ,
      (Matrix.trace (Z.conjTranspose * Z)).re
        ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
      (N : ℝ) * (K : ℝ) := by
  have hM : 1 ≤ M := by omega
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := by omega
  let e := rectangularConjTransposeMeasurableEquiv K N
  let g : Matrix (Fin N) (Fin K) ℂ → ℝ := fun Z ↦
    (Matrix.trace (Z * Z.conjTranspose)).re
  have hg : Measurable g := by
    dsimp only [g]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    fun_prop
  calc
    (∫ Z : Matrix (Fin K) (Fin N) ℂ,
      (Matrix.trace (Z.conjTranspose * Z)).re
        ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
      ∫ Z : Matrix (Fin K) (Fin N) ℂ, g (e Z)
        ∂(jiangSqrtScaledTallHaarCornerLaw M K N) := by
          apply integral_congr_ae
          filter_upwards [] with Z
          simp only [g, e,
            rectangularConjTransposeMeasurableEquiv_apply,
            Matrix.conjTranspose_conjTranspose]
    _ = ∫ Z : Matrix (Fin N) (Fin K) ℂ, g Z
        ∂Measure.map e (jiangSqrtScaledTallHaarCornerLaw M K N) := by
      exact (integral_map e.measurable.aemeasurable
        hg.aestronglyMeasurable).symm
    _ = ∫ Z : Matrix (Fin N) (Fin K) ℂ, g Z
        ∂(sqrtScaledHaarBlockLaw
          canonicalUnitaryHaarProbabilityFamily M N K) := by
      rw [map_rectangularConjTranspose_jiangSqrtScaledTallHaarCornerLaw
        hNK hs]
    _ = (N : ℝ) * (K : ℝ) :=
      integral_rowGramEnergy_sqrtScaledHaarBlockLaw_canonical
        hM hNM hKM

/-- The squared column-Gram energy is integrable under Jiang's scaled tall
corner law. -/
theorem integrable_jiangSqrtScaledTallHaarCorner_gramSecondEnergy
    {M K N : ℕ} (hNK : N ≤ K) (hs : K + N ≤ M) :
    Integrable
      (fun Z : Matrix (Fin K) (Fin N) ℂ ↦
        (Matrix.trace ((Z.conjTranspose * Z) *
          (Z.conjTranspose * Z))).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N) := by
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := by omega
  let e := rectangularConjTransposeMeasurableEquiv K N
  let g : Matrix (Fin N) (Fin K) ℂ → ℝ := fun Z ↦
    (Matrix.trace ((Z * Z.conjTranspose) *
      (Z * Z.conjTranspose))).re
  have hg : Measurable g := by
    dsimp only [g]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    fun_prop
  have hwide :=
    integrable_rowGramSecondEnergy_sqrtScaledHaarBlockLaw_canonical hNM hKM
  rw [← map_rectangularConjTranspose_jiangSqrtScaledTallHaarCornerLaw
    hNK hs] at hwide
  have hcomp := (integrable_map_measure hg.aestronglyMeasurable
    e.measurable.aemeasurable).mp hwide
  exact hcomp.congr (ae_of_all _ fun Z ↦ by
    simp only [g, e, Function.comp_apply,
      rectangularConjTransposeMeasurableEquiv_apply,
      Matrix.conjTranspose_conjTranspose])

/-- Exact squared column-Gram energy under Jiang's scaled tall law. -/
theorem integral_jiangSqrtScaledTallHaarCorner_gramSecondEnergy
    {M K N : ℕ} (hM2 : 2 ≤ M) (hN : 0 < N)
    (hNK : N ≤ K) (hs : K + N ≤ M) :
    (∫ Z : Matrix (Fin K) (Fin N) ℂ,
      (Matrix.trace ((Z.conjTranspose * Z) *
        (Z.conjTranspose * Z))).re
        ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
      (N : ℝ) * K * M *
          ((M : ℝ) * ((N : ℝ) + K) - (N : ℝ) * K - 1) /
        ((M : ℝ) ^ 2 - 1) := by
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := by omega
  let e := rectangularConjTransposeMeasurableEquiv K N
  let g : Matrix (Fin N) (Fin K) ℂ → ℝ := fun Z ↦
    (Matrix.trace ((Z * Z.conjTranspose) *
      (Z * Z.conjTranspose))).re
  have hg : Measurable g := by
    dsimp only [g]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    fun_prop
  calc
    (∫ Z : Matrix (Fin K) (Fin N) ℂ,
      (Matrix.trace ((Z.conjTranspose * Z) *
        (Z.conjTranspose * Z))).re
        ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
      ∫ Z : Matrix (Fin K) (Fin N) ℂ, g (e Z)
        ∂(jiangSqrtScaledTallHaarCornerLaw M K N) := by
          apply integral_congr_ae
          filter_upwards [] with Z
          simp only [g, e,
            rectangularConjTransposeMeasurableEquiv_apply,
            Matrix.conjTranspose_conjTranspose]
    _ = ∫ Z : Matrix (Fin N) (Fin K) ℂ, g Z
        ∂Measure.map e (jiangSqrtScaledTallHaarCornerLaw M K N) := by
      exact (integral_map e.measurable.aemeasurable
        hg.aestronglyMeasurable).symm
    _ = ∫ Z : Matrix (Fin N) (Fin K) ℂ, g Z
        ∂(sqrtScaledHaarBlockLaw
          canonicalUnitaryHaarProbabilityFamily M N K) := by
      rw [map_rectangularConjTranspose_jiangSqrtScaledTallHaarCornerLaw
        hNK hs]
    _ = _ :=
      integral_rowGramSecondEnergy_sqrtScaledHaarBlockLaw_canonical
        hM2 hN hNM hKM

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
