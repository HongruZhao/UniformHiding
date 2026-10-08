import A3.Target

open scoped Matrix Matrix.Norms.Elementwise
open MeasureTheory

noncomputable section

namespace A3Research

instance (priority := 100) hermitianAmbientMatrixMeasurableSpace
    (ι κ K : Type*) [MeasurableSpace K] : MeasurableSpace (Matrix ι κ K) :=
  inferInstanceAs (MeasurableSpace (ι → κ → K))

instance (priority := 100) hermitianAmbientMatrixBorelSpace
    (ι κ K : Type*) [Fintype ι] [Fintype κ] [RCLike K]
    [MeasurableSpace K] [BorelSpace K] : BorelSpace (Matrix ι κ K) :=
  inferInstanceAs (BorelSpace (ι → κ → K))

/-- The independent strict upper-triangular entries. -/
abbrev HermitianCoordinateIndex (n : ℕ) :=
  {ij : Fin n × Fin n // ij.1 < ij.2}

/-- Actual independent Hermitian coordinates: real diagonal, then upper entries. -/
abbrev HermitianCoordinates (n : ℕ) (K : Type*) :=
  (Fin n → ℝ) × (HermitianCoordinateIndex n → K)

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianMatrixOfCoordinates (x : HermitianCoordinates n K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j ↦ if h : i = j then (x.1 i : K)
    else if hlt : i < j then x.2 ⟨(i, j), hlt⟩
    else star (x.2 ⟨(j, i), lt_of_le_of_ne (le_of_not_gt hlt) (fun hji ↦ h hji.symm)⟩)

@[simp] theorem hermitianMatrixOfCoordinates_diag (x : HermitianCoordinates n K)
    (i : Fin n) : hermitianMatrixOfCoordinates x i i = (x.1 i : K) := by
  simp [hermitianMatrixOfCoordinates]

@[simp] theorem hermitianMatrixOfCoordinates_upper (x : HermitianCoordinates n K)
    (ij : HermitianCoordinateIndex n) :
    hermitianMatrixOfCoordinates x ij.1.1 ij.1.2 = x.2 ij := by
  simp [hermitianMatrixOfCoordinates, ij.2, ne_of_lt ij.2]

@[simp] theorem hermitianMatrixOfCoordinates_lower (x : HermitianCoordinates n K)
    (ij : HermitianCoordinateIndex n) :
    hermitianMatrixOfCoordinates x ij.1.2 ij.1.1 = star (x.2 ij) := by
  simp [hermitianMatrixOfCoordinates, ne_of_gt ij.2, not_lt_of_ge ij.2.le]

theorem hermitianMatrixOfCoordinates_isHermitian (x : HermitianCoordinates n K) :
    (hermitianMatrixOfCoordinates x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [hermitianMatrixOfCoordinates_lower x ⟨(i, j), hij⟩,
      hermitianMatrixOfCoordinates_upper x ⟨(i, j), hij⟩]
    simp
  · subst j
    simp
  · rw [hermitianMatrixOfCoordinates_lower x ⟨(j, i), hij⟩,
      hermitianMatrixOfCoordinates_upper x ⟨(j, i), hij⟩]

def hermitianCoordinateProjection (H : Matrix (Fin n) (Fin n) K) :
    HermitianCoordinates n K :=
  (fun i ↦ RCLike.re (H i i), fun ij ↦ H ij.1.1 ij.1.2)

@[simp] theorem hermitianCoordinateProjection_ofCoordinates (x : HermitianCoordinates n K) :
    hermitianCoordinateProjection (hermitianMatrixOfCoordinates x) = x := by
  apply Prod.ext
  · funext i
    simp [hermitianCoordinateProjection]
  · funext ij
    simp [hermitianCoordinateProjection]

theorem hermitianMatrixOfCoordinates_projection (H : Matrix (Fin n) (Fin n) K)
    (hH : H.IsHermitian) :
    hermitianMatrixOfCoordinates (hermitianCoordinateProjection H) = H := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simpa [hermitianCoordinateProjection] using
      hermitianMatrixOfCoordinates_upper (hermitianCoordinateProjection H)
      ⟨(i, j), hij⟩
  · subst j
    simpa [hermitianCoordinateProjection] using
      (RCLike.conj_eq_iff_re.mp (hH.apply i i))
  · simpa [hermitianCoordinateProjection] using
      (hermitianMatrixOfCoordinates_lower (hermitianCoordinateProjection H)
        ⟨(j, i), hij⟩).trans (hH.apply i j)

def hermitianMatrixSubmodule (n : ℕ) (K : Type*) [RCLike K] :
    Submodule ℝ (Matrix (Fin n) (Fin n) K) where
  carrier := {H | H.IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' := fun hH hG ↦ hH.add hG
  smul_mem' := fun r _ hH ↦ hH.smul (IsSelfAdjoint.all r)

def hermitianMatrixOfCoordinatesLinearMap (n : ℕ) (K : Type*) [RCLike K] :
    HermitianCoordinates n K →ₗ[ℝ] Matrix (Fin n) (Fin n) K where
  toFun := hermitianMatrixOfCoordinates
  map_add' := by
    intro x y
    ext i j
    by_cases hij : i = j
    · simp [hermitianMatrixOfCoordinates, hij]
    · by_cases hlt : i < j <;> simp [hermitianMatrixOfCoordinates, hij, hlt]
  map_smul' := by
    intro r x
    ext i j
    by_cases hij : i = j
    · simp [hermitianMatrixOfCoordinates, hij, RCLike.real_smul_eq_coe_mul]
    · by_cases hlt : i < j <;>
        simp [hermitianMatrixOfCoordinates, hij, hlt, RCLike.real_smul_eq_coe_mul]

def hermitianCoordinateProjectionLinearMap (n : ℕ) (K : Type*) [RCLike K] :
    Matrix (Fin n) (Fin n) K →ₗ[ℝ] HermitianCoordinates n K where
  toFun := hermitianCoordinateProjection
  map_add' := by
    intro H G
    apply Prod.ext <;> funext i <;> simp [hermitianCoordinateProjection]
  map_smul' := by
    intro r H
    apply Prod.ext <;> funext i <;>
      simp [hermitianCoordinateProjection, RCLike.real_smul_eq_coe_mul]

/-- The real-linear coordinate equivalence to the full Hermitian space. -/
def hermitianCoordinatesLinearEquiv (n : ℕ) (K : Type*) [RCLike K] :
    HermitianCoordinates n K ≃ₗ[ℝ] hermitianMatrixSubmodule n K where
  toFun := fun x ↦ ⟨hermitianMatrixOfCoordinates x,
    hermitianMatrixOfCoordinates_isHermitian x⟩
  invFun := fun H ↦ hermitianCoordinateProjection H.1
  left_inv := hermitianCoordinateProjection_ofCoordinates
  right_inv := fun H ↦ Subtype.ext (hermitianMatrixOfCoordinates_projection H.1 H.2)
  map_add' := fun x y ↦ Subtype.ext ((hermitianMatrixOfCoordinatesLinearMap n K).map_add x y)
  map_smul' := fun r x ↦ Subtype.ext ((hermitianMatrixOfCoordinatesLinearMap n K).map_smul r x)

theorem continuous_hermitianMatrixOfCoordinates :
    Continuous (hermitianMatrixOfCoordinates : HermitianCoordinates n K → _) :=
  (hermitianMatrixOfCoordinatesLinearMap n K).continuous_of_finiteDimensional

theorem continuous_hermitianCoordinateProjection :
    Continuous (hermitianCoordinateProjection : Matrix (Fin n) (Fin n) K → _) :=
  (hermitianCoordinateProjectionLinearMap n K).continuous_of_finiteDimensional

section Volume

variable (n : ℕ) (K : Type*) [RCLike K] [MeasureSpace K] [BorelSpace K]

/-- Flat volume in the literal independent coordinates, with diagonal first. -/
def hermitianCoordinateVolume : Measure (HermitianCoordinates n K) :=
  (volume : Measure (Fin n → ℝ)).prod
    (volume : Measure (HermitianCoordinateIndex n → K))

/-- The induced measure on the actual real-symmetric or complex-Hermitian matrices. -/
def hermitianMatrixVolume : Measure (Matrix (Fin n) (Fin n) K) :=
  Measure.map hermitianMatrixOfCoordinates (hermitianCoordinateVolume n K)

theorem measurable_hermitianMatrixOfCoordinates :
    Measurable (hermitianMatrixOfCoordinates : HermitianCoordinates n K → _) :=
  continuous_hermitianMatrixOfCoordinates.measurable

theorem measurable_hermitianCoordinateProjection :
    Measurable (hermitianCoordinateProjection : Matrix (Fin n) (Fin n) K → _) :=
  continuous_hermitianCoordinateProjection.measurable

end Volume

end A3Research
