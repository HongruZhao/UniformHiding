import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_HaarLastColumnUniform
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerBaseColumn
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerConditionalOrbit
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarSuffixBlock
import LogdetLean.FixedSubspaceGaussian
import LogdetLean.GaussianSubspace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# A Gaussian construction of the next Haar--Stiefel column

For a fixed matrix `Q` with orthonormal columns, the orthogonal projection
`(I - Q Qᴴ) g` of an ambient standard Gaussian lies in the orthogonal
complement of the columns of `Q`.  Normalizing it gives the usual candidate
for the next column in the Haar--Stiefel recursion.

This file records the measurable construction and its deterministic support
and unitary-equivariance properties.  It deliberately does not postulate a
regular conditional distribution or a measurable choice of an orthonormal
basis of the complement.
-/

open MeasureTheory ProbabilityTheory Matrix Metric
open scoped RealInnerProductSpace InnerProductSpace MeasureTheory Matrix
  ComplexOrder MatrixOrder BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

local instance h19HaarStiefelNextColumnMatrixBorelSpace (M L : ℕ) :
    BorelSpace (Matrix (Fin M) (Fin L) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin M → Fin L → ℂ))

/-! ## The projected-Gaussian construction -/

/-- The Hermitian complement-projection candidate `I - Q Qᴴ`. -/
def h19StiefelComplementMatrix {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  1 - Q * Q.conjTranspose

/-- Project an ambient Euclidean vector by `I - Q Qᴴ`. -/
def h19StiefelProjectedGaussian {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (g : EuclideanSpace ℂ (Fin M)) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2
    (h19StiefelComplementMatrix Q *ᵥ WithLp.ofLp g)

/-- Totalized normalized projected Gaussian.  Its value is zero exactly on
the null exceptional event where the projection vanishes. -/
def h19StiefelNextColumn {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (g : EuclideanSpace ℂ (Fin M)) : EuclideanSpace ℂ (Fin M) :=
  LogdetLean.unitDirection (h19StiefelProjectedGaussian Q g)

/-- The candidate conditional next-column law for a fixed past frame `Q`. -/
def h19StiefelNextColumnLaw {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) :
    Measure (EuclideanSpace ℂ (Fin M)) :=
  Measure.map (h19StiefelNextColumn Q)
    (stdGaussian (EuclideanSpace ℂ (Fin M)))

/-- The complex-linear column map of a partial frame. -/
def h19StiefelColumnLinearMap {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) :
    EuclideanSpace ℂ (Fin L) →ₗ[ℂ] EuclideanSpace ℂ (Fin M) :=
  (WithLp.linearEquiv 2 ℂ (Fin M → ℂ)).symm.toLinearMap.comp
    (Q.mulVecLin.comp
      (WithLp.linearEquiv 2 ℂ (Fin L → ℂ)).toLinearMap)

@[simp]
theorem h19StiefelColumnLinearMap_apply {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (x : EuclideanSpace ℂ (Fin L)) :
    h19StiefelColumnLinearMap Q x =
      WithLp.toLp 2 (Q *ᵥ WithLp.ofLp x) := by
  rfl

/-- The complex span of the already exposed columns. -/
def h19StiefelColumnSpan {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin M)) :=
  (h19StiefelColumnLinearMap Q).range

/-- The same column span regarded as a real subspace, as required by the
real standard-Gaussian projection API. -/
def h19StiefelColumnRealSpan {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) :
    Submodule ℝ (EuclideanSpace ℂ (Fin M)) :=
  (h19StiefelColumnSpan Q).restrictScalars ℝ

/-- Fewer columns than ambient coordinates always span a proper real
subspace.  No Stiefel assumption is needed for this dimension bound. -/
theorem h19StiefelColumnRealSpan_ne_top {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) (hLM : L < M) :
    h19StiefelColumnRealSpan Q ≠ ⊤ := by
  have hcomplex : h19StiefelColumnSpan Q ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective (h19StiefelColumnLinearMap Q) :=
      LinearMap.range_eq_top.mp htop
    have hdim := LinearMap.finrank_le_finrank_of_surjective hsurj
    have hML : M ≤ L := by
      simpa using hdim
    exact (Nat.not_le_of_lt hLM) hML
  intro hreal
  apply hcomplex
  apply top_unique
  intro x _hx
  have hx : x ∈ h19StiefelColumnRealSpan Q := by
    rw [hreal]
    trivial
  exact hx

/-- If the complement projection vanishes, the ambient vector belongs to
the column span. -/
theorem h19StiefelProjectedGaussian_eq_zero_mem_columnRealSpan
    {M L : ℕ} (Q : Matrix (Fin M) (Fin L) ℂ)
    (g : EuclideanSpace ℂ (Fin M))
    (hg : h19StiefelProjectedGaussian Q g = 0) :
    g ∈ h19StiefelColumnRealSpan Q := by
  have hgraw := congrArg WithLp.ofLp hg
  change h19StiefelComplementMatrix Q *ᵥ WithLp.ofLp g = 0 at hgraw
  rw [h19StiefelComplementMatrix, Matrix.sub_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at hgraw
  have heq : WithLp.ofLp g =
      Q *ᵥ (Q.conjTranspose *ᵥ WithLp.ofLp g) :=
    sub_eq_zero.mp hgraw
  change g ∈ h19StiefelColumnSpan Q
  refine ⟨WithLp.toLp 2
    (Q.conjTranspose *ᵥ WithLp.ofLp g), ?_⟩
  apply WithLp.ofLp_injective 2
  simpa using heq.symm

/-- The exceptional event where normalization is totalized at zero has
standard-Gaussian measure zero whenever fewer than `M` columns have already
been exposed. -/
theorem h19StiefelProjectedGaussian_eq_zero_null {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) (hLM : L < M) :
    stdGaussian (EuclideanSpace ℂ (Fin M))
        {g | h19StiefelProjectedGaussian Q g = 0} = 0 := by
  apply measure_mono_null
    (fun _g hg ↦
      h19StiefelProjectedGaussian_eq_zero_mem_columnRealSpan Q _ hg)
  exact LogdetLean.stdGaussian_proper_submodule_null
    (h19StiefelColumnRealSpan Q)
    (h19StiefelColumnRealSpan_ne_top Q hLM)

theorem ae_h19StiefelProjectedGaussian_ne_zero {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) (hLM : L < M) :
    ∀ᵐ g ∂stdGaussian (EuclideanSpace ℂ (Fin M)),
      h19StiefelProjectedGaussian Q g ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not] using
    h19StiefelProjectedGaussian_eq_zero_null Q hLM

theorem continuous_h19StiefelProjectedGaussian_uncurry (M L : ℕ) :
    Continuous (fun p : Matrix (Fin M) (Fin L) ℂ ×
        EuclideanSpace ℂ (Fin M) ↦
      h19StiefelProjectedGaussian p.1 p.2) := by
  unfold h19StiefelProjectedGaussian h19StiefelComplementMatrix
  fun_prop

theorem measurable_h19StiefelProjectedGaussian_uncurry (M L : ℕ) :
    Measurable (fun p : Matrix (Fin M) (Fin L) ℂ ×
        EuclideanSpace ℂ (Fin M) ↦
      h19StiefelProjectedGaussian p.1 p.2) :=
  (continuous_h19StiefelProjectedGaussian_uncurry M L).measurable

theorem measurable_h19StiefelProjectedGaussian {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) :
    Measurable (h19StiefelProjectedGaussian Q) := by
  unfold h19StiefelProjectedGaussian h19StiefelComplementMatrix
  fun_prop

theorem measurable_h19StiefelNextColumn_uncurry (M L : ℕ) :
    Measurable (fun p : Matrix (Fin M) (Fin L) ℂ ×
        EuclideanSpace ℂ (Fin M) ↦
      h19StiefelNextColumn p.1 p.2) := by
  exact LogdetLean.measurable_unitDirection.comp
    (measurable_h19StiefelProjectedGaussian_uncurry M L)

theorem measurable_h19StiefelNextColumn {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) :
    Measurable (h19StiefelNextColumn Q) := by
  exact LogdetLean.measurable_unitDirection.comp
    (measurable_h19StiefelProjectedGaussian Q)

/-! ## Deterministic projection and support algebra -/

/-- Under the Stiefel relation `QᴴQ=I`, `I-QQᴴ` kills the columns of
`Q` from the left. -/
theorem conjTranspose_mul_h19StiefelComplementMatrix {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    Q.conjTranspose * h19StiefelComplementMatrix Q = 0 := by
  rw [h19StiefelComplementMatrix, Matrix.mul_sub, Matrix.mul_one,
    ← Matrix.mul_assoc, hQ, Matrix.one_mul, sub_self]

/-- `I-QQᴴ` is idempotent when the columns of `Q` are orthonormal. -/
theorem h19StiefelComplementMatrix_mul_self {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    h19StiefelComplementMatrix Q * h19StiefelComplementMatrix Q =
      h19StiefelComplementMatrix Q := by
  have hproj :
      (Q * Q.conjTranspose) * (Q * Q.conjTranspose) =
        Q * Q.conjTranspose := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q.conjTranspose Q,
      hQ, Matrix.one_mul]
  unfold h19StiefelComplementMatrix
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    hproj, sub_self, sub_zero]

/-- `I-QQᴴ` is Hermitian. -/
theorem h19StiefelComplementMatrix_conjTranspose {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) :
    (h19StiefelComplementMatrix Q).conjTranspose =
      h19StiefelComplementMatrix Q := by
  simp [h19StiefelComplementMatrix, Matrix.conjTranspose_mul]

/-- The projected vector is orthogonal to every previous column. -/
theorem h19StiefelProjectedGaussian_orthogonal_columns {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1)
    (g : EuclideanSpace ℂ (Fin M)) :
    Q.conjTranspose *ᵥ WithLp.ofLp (h19StiefelProjectedGaussian Q g) = 0 := by
  change Q.conjTranspose *ᵥ
      (h19StiefelComplementMatrix Q *ᵥ WithLp.ofLp g) = 0
  rw [Matrix.mulVec_mulVec,
    conjTranspose_mul_h19StiefelComplementMatrix Q hQ, Matrix.zero_mulVec]

/-- In complex inner-product form, every vector in the column range is
orthogonal to the projected Gaussian. -/
theorem h19StiefelColumnLinearMap_inner_projectedGaussian {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1)
    (c : EuclideanSpace ℂ (Fin L))
    (g : EuclideanSpace ℂ (Fin M)) :
    ⟪h19StiefelColumnLinearMap Q c,
      h19StiefelProjectedGaussian Q g⟫_ℂ = 0 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,
    h19StiefelColumnLinearMap_apply]
  rw [dotProduct_comm]
  change star (Q *ᵥ WithLp.ofLp c) ⬝ᵥ
      WithLp.ofLp (h19StiefelProjectedGaussian Q g) = 0
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    h19StiefelProjectedGaussian_orthogonal_columns Q hQ g]
  simp

/-- The projected Gaussian belongs to the real orthogonal complement of
the previous complex column span. -/
theorem h19StiefelProjectedGaussian_mem_orthogonal_columnRealSpan
    {M L : ℕ} (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1)
    (g : EuclideanSpace ℂ (Fin M)) :
    h19StiefelProjectedGaussian Q g ∈
      (h19StiefelColumnRealSpan Q)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro x hx
  change x ∈ h19StiefelColumnSpan Q at hx
  rcases hx with ⟨c, rfl⟩
  have hcx := h19StiefelColumnLinearMap_inner_projectedGaussian
    Q hQ c g
  have hxc : ⟪h19StiefelProjectedGaussian Q g,
      h19StiefelColumnLinearMap Q c⟫_ℂ = 0 :=
    inner_eq_zero_symm.mp hcx
  have hre :
      ⟪h19StiefelProjectedGaussian Q g,
          h19StiefelColumnLinearMap Q c⟫_ℝ =
        Complex.re ⟪h19StiefelProjectedGaussian Q g,
          h19StiefelColumnLinearMap Q c⟫_ℂ := by
    simp only [PiLp.inner_apply, real_inner_eq_re_inner ℂ]
    exact (Complex.re_sum (s := Finset.univ)
      (fun i ↦ ⟪WithLp.ofLp (h19StiefelProjectedGaussian Q g) i,
        WithLp.ofLp (h19StiefelColumnLinearMap Q c) i⟫_ℂ)).symm
  rw [hre, hxc]
  rfl

/-- The removed component `g - (I-QQᴴ)g` lies in the column range. -/
theorem sub_h19StiefelProjectedGaussian_mem_columnRealSpan
    {M L : ℕ} (Q : Matrix (Fin M) (Fin L) ℂ)
    (g : EuclideanSpace ℂ (Fin M)) :
    g - h19StiefelProjectedGaussian Q g ∈
      h19StiefelColumnRealSpan Q := by
  change g - h19StiefelProjectedGaussian Q g ∈
    h19StiefelColumnSpan Q
  refine ⟨WithLp.toLp 2
    (Q.conjTranspose *ᵥ WithLp.ofLp g), ?_⟩
  apply WithLp.ofLp_injective 2
  change Q *ᵥ (Q.conjTranspose *ᵥ WithLp.ofLp g) =
    WithLp.ofLp g -
      h19StiefelComplementMatrix Q *ᵥ WithLp.ofLp g
  rw [h19StiefelComplementMatrix, Matrix.sub_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  abel

/-- For a Stiefel frame, the matrix formula is exactly the Hilbert-space
orthogonal projection onto the real orthogonal complement of the column
span. -/
theorem coe_orthogonalComplementProjection_eq_h19StiefelProjectedGaussian
    {M L : ℕ} (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1)
    (g : EuclideanSpace ℂ (Fin M)) :
    ((((h19StiefelColumnRealSpan Q)ᗮ).orthogonalProjectionOnto g :
        (h19StiefelColumnRealSpan Q)ᗮ) :
      EuclideanSpace ℂ (Fin M)) =
        h19StiefelProjectedGaussian Q g := by
  let K := h19StiefelColumnRealSpan Q
  apply Kᗮ.eq_starProjection_of_mem_orthogonal
  · exact h19StiefelProjectedGaussian_mem_orthogonal_columnRealSpan Q hQ g
  · exact K.le_orthogonal_orthogonal
      (sub_h19StiefelProjectedGaussian_mem_columnRealSpan Q g)

/-- Normalization preserves orthogonality to the previous columns. -/
theorem h19StiefelNextColumn_orthogonal_columns {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1)
    (g : EuclideanSpace ℂ (Fin M)) :
    Q.conjTranspose *ᵥ WithLp.ofLp (h19StiefelNextColumn Q g) = 0 := by
  classical
  by_cases hg : h19StiefelProjectedGaussian Q g = 0
  · simp [h19StiefelNextColumn, LogdetLean.unitDirection, hg]
  · rw [h19StiefelNextColumn, LogdetLean.unitDirection, if_neg hg]
    rw [WithLp.ofLp_smul]
    change Q.conjTranspose *ᵥ
      (‖h19StiefelProjectedGaussian Q g‖⁻¹ •
        WithLp.ofLp (h19StiefelProjectedGaussian Q g)) = 0
    rw [Matrix.mulVec_smul,
      h19StiefelProjectedGaussian_orthogonal_columns Q hQ g, smul_zero]

/-- Away from the zero-projection exceptional event, the new column has
unit norm. -/
theorem norm_h19StiefelNextColumn_of_ne_zero {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (g : EuclideanSpace ℂ (Fin M))
    (hg : h19StiefelProjectedGaussian Q g ≠ 0) :
    ‖h19StiefelNextColumn Q g‖ = 1 := by
  rw [h19StiefelNextColumn, LogdetLean.unitDirection, if_neg hg,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg)

/-! ## Exact fixed-frame laws -/

/-- The unnormalized matrix projection has exactly the ambient inclusion of
a standard Gaussian on the orthogonal complement. -/
theorem map_h19StiefelProjectedGaussian_stdGaussian
    {M L : ℕ} (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    Measure.map (h19StiefelProjectedGaussian Q)
        (stdGaussian (EuclideanSpace ℂ (Fin M))) =
      Measure.map (Subtype.val :
          (h19StiefelColumnRealSpan Q)ᗮ →
            EuclideanSpace ℂ (Fin M))
        (stdGaussian ((h19StiefelColumnRealSpan Q)ᗮ)) := by
  let K := h19StiefelColumnRealSpan Q
  have hproj := LogdetLean.hasLaw_orthogonalComplementProjection_stdGaussian K
  calc
    Measure.map (h19StiefelProjectedGaussian Q)
        (stdGaussian (EuclideanSpace ℂ (Fin M))) =
        Measure.map (fun g : EuclideanSpace ℂ (Fin M) ↦
          (((Kᗮ).orthogonalProjectionOnto g : Kᗮ) :
            EuclideanSpace ℂ (Fin M)))
          (stdGaussian (EuclideanSpace ℂ (Fin M))) := by
      apply Measure.map_congr
      filter_upwards [] with g
      exact (coe_orthogonalComplementProjection_eq_h19StiefelProjectedGaussian
        Q hQ g).symm
    _ = Measure.map (Subtype.val : Kᗮ → EuclideanSpace ℂ (Fin M))
        (Measure.map (Kᗮ).orthogonalProjectionOnto
          (stdGaussian (EuclideanSpace ℂ (Fin M)))) := by
      rw [Measure.map_map measurable_subtype_coe
        (Kᗮ).orthogonalProjectionOnto.measurable]
      rfl
    _ = Measure.map (Subtype.val : Kᗮ → EuclideanSpace ℂ (Fin M))
        (stdGaussian Kᗮ) := by rw [hproj.map_eq]

/-- After normalization, the candidate law is exactly the ambient inclusion
of the normalized direction of a standard Gaussian living in the orthogonal
complement. -/
theorem map_h19StiefelNextColumn_stdGaussian_eq_complementDirection
    {M L : ℕ} (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    h19StiefelNextColumnLaw Q =
      Measure.map
        (fun z : (h19StiefelColumnRealSpan Q)ᗮ ↦
          LogdetLean.unitDirection
            (z : EuclideanSpace ℂ (Fin M)))
        (stdGaussian ((h19StiefelColumnRealSpan Q)ᗮ)) := by
  let K := h19StiefelColumnRealSpan Q
  calc
    h19StiefelNextColumnLaw Q =
        Measure.map LogdetLean.unitDirection
          (Measure.map (h19StiefelProjectedGaussian Q)
            (stdGaussian (EuclideanSpace ℂ (Fin M)))) := by
      rw [Measure.map_map LogdetLean.measurable_unitDirection
        (measurable_h19StiefelProjectedGaussian Q)]
      rfl
    _ = Measure.map LogdetLean.unitDirection
        (Measure.map (Subtype.val : Kᗮ → EuclideanSpace ℂ (Fin M))
          (stdGaussian Kᗮ)) := by
      rw [map_h19StiefelProjectedGaussian_stdGaussian Q hQ]
    _ = Measure.map
        (fun z : Kᗮ ↦ LogdetLean.unitDirection
          (z : EuclideanSpace ℂ (Fin M))) (stdGaussian Kᗮ) := by
      rw [Measure.map_map LogdetLean.measurable_unitDirection
        measurable_subtype_coe]
      rfl

/-- Taking unit direction commutes with including a real subspace into its
ambient normed space. -/
theorem h19_unitDirection_subtype_val
    {M : ℕ} (K : Submodule ℝ (EuclideanSpace ℂ (Fin M))) (z : K) :
    LogdetLean.unitDirection (z : EuclideanSpace ℂ (Fin M)) =
      (LogdetLean.unitDirection z : K) := by
  classical
  by_cases hz : z = 0
  · simp [hz, LogdetLean.unitDirection]
  · have hzcoe : (z : EuclideanSpace ℂ (Fin M)) ≠ 0 :=
      Subtype.coe_ne_coe.mpr hz
    simp [LogdetLean.unitDirection, hz, hzcoe]

/-- The Stiefel relation gives injectivity of the column map. -/
theorem h19StiefelColumnLinearMap_injective {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    Function.Injective (h19StiefelColumnLinearMap Q) := by
  intro x y hxy
  apply WithLp.ofLp_injective 2
  have hxyraw := congrArg WithLp.ofLp hxy
  change Q *ᵥ WithLp.ofLp x = Q *ᵥ WithLp.ofLp y at hxyraw
  have hleft := congrArg (fun z ↦ Q.conjTranspose *ᵥ z) hxyraw
  simpa only [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] using hleft

/-- A Stiefel frame with `L` columns has complex column-span dimension `L`. -/
theorem finrank_h19StiefelColumnSpan {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    Module.finrank ℂ (h19StiefelColumnSpan Q) = L := by
  unfold h19StiefelColumnSpan
  rw [LinearMap.finrank_range_of_inj
    (h19StiefelColumnLinearMap_injective Q hQ)]
  simp

/-- The same span has real dimension `2L`. -/
theorem real_finrank_h19StiefelColumnRealSpan {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    Module.finrank ℝ (h19StiefelColumnRealSpan Q) = 2 * L := by
  change Module.finrank ℝ (h19StiefelColumnSpan Q) = 2 * L
  rw [← Module.finrank_mul_finrank ℝ ℂ (h19StiefelColumnSpan Q),
    finrank_h19StiefelColumnSpan Q hQ]
  norm_num

/-- Consequently the orthogonal complement has real dimension
`2(M-L)`, i.e. complex spherical dimension `M-L`. -/
theorem real_finrank_h19StiefelColumnRealSpan_orthogonal {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    Module.finrank ℝ ((h19StiefelColumnRealSpan Q)ᗮ) =
      2 * (M - L) := by
  let K := h19StiefelColumnRealSpan Q
  have hsum := K.finrank_add_finrank_orthogonal
  have hamb : Module.finrank ℝ (EuclideanSpace ℂ (Fin M)) = 2 * M := by
    rw [← Module.finrank_mul_finrank ℝ ℂ
      (EuclideanSpace ℂ (Fin M))]
    norm_num
  have hLM : L ≤ M := by
    have hdim := LinearMap.finrank_le_finrank_of_injective
      (h19StiefelColumnLinearMap_injective Q hQ)
    simpa using hdim
  have hsum' : 2 * L +
      Module.finrank ℝ ((h19StiefelColumnRealSpan Q)ᗮ) = 2 * M := by
    simpa only [K, real_finrank_h19StiefelColumnRealSpan Q hQ, hamb]
      using hsum
  omega

/-- In the next-column indexing `L=N-1`, the complement is the real form of
a complex space of dimension `M-N+1`. -/
theorem real_finrank_h19StiefelNextColumnComplement {M N : ℕ}
    (Q : Matrix (Fin M) (Fin (N - 1)) ℂ)
    (hQ : Q.conjTranspose * Q = 1) (hN : 1 ≤ N) (hNM : N ≤ M) :
    Module.finrank ℝ ((h19StiefelColumnRealSpan Q)ᗮ) =
      2 * (M - N + 1) := by
  rw [real_finrank_h19StiefelColumnRealSpan_orthogonal Q hQ]
  omega

/-- Properness of the previous-column span supplies a nontrivial orthogonal
complement. -/
theorem h19StiefelOrthogonalComplementNontrivial {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) (hLM : L < M) :
    Nontrivial ((h19StiefelColumnRealSpan Q)ᗮ) :=
  Submodule.nontrivial_iff_ne_bot.mpr (by
    intro hbot
    exact h19StiefelColumnRealSpan_ne_top Q hLM
      (Submodule.orthogonal_eq_bot_iff.mp hbot))

/-- Uniform surface probability on the unit sphere of the orthogonal
complement, included into the ambient Euclidean space. -/
def h19StiefelComplementUniformSphereLaw {M L : ℕ}
    (Q : Matrix (Fin M) (Fin L) ℂ) (hLM : L < M) :
    Measure (EuclideanSpace ℂ (Fin M)) := by
  letI := h19StiefelOrthogonalComplementNontrivial Q hLM
  exact Measure.map
    (fun s : sphere (0 : (h19StiefelColumnRealSpan Q)ᗮ) 1 ↦
      ((s.1 : (h19StiefelColumnRealSpan Q)ᗮ) :
        EuclideanSpace ℂ (Fin M)))
    (LogdetLean.uniformSphereSurfaceMeasure
      (E := (h19StiefelColumnRealSpan Q)ᗮ))

/-- Exact fixed-frame law: normalizing `(I-QQᴴ)g` is surface-uniform on
the unit sphere of the orthogonal complement of the previous columns. -/
theorem map_h19StiefelNextColumn_stdGaussian_eq_uniformComplementSphere
    {M L : ℕ} (Q : Matrix (Fin M) (Fin L) ℂ)
    (hQ : Q.conjTranspose * Q = 1) (hLM : L < M) :
    h19StiefelNextColumnLaw Q =
      h19StiefelComplementUniformSphereLaw Q hLM := by
  let K := h19StiefelColumnRealSpan Q
  letI : Nontrivial Kᗮ := h19StiefelOrthogonalComplementNontrivial Q hLM
  rw [map_h19StiefelNextColumn_stdGaussian_eq_complementDirection Q hQ]
  unfold h19StiefelComplementUniformSphereLaw
  calc
    Measure.map (fun z : Kᗮ ↦ LogdetLean.unitDirection
        (z : EuclideanSpace ℂ (Fin M))) (stdGaussian Kᗮ) =
        Measure.map (Subtype.val : Kᗮ → EuclideanSpace ℂ (Fin M))
          (Measure.map LogdetLean.unitDirection (stdGaussian Kᗮ)) := by
      rw [Measure.map_map measurable_subtype_coe
        LogdetLean.measurable_unitDirection]
      apply Measure.map_congr
      filter_upwards [] with z
      exact h19_unitDirection_subtype_val (Kᗮ) z
    _ = Measure.map (Subtype.val : Kᗮ → EuclideanSpace ℂ (Fin M))
        (Measure.map
          (Subtype.val : sphere (0 : Kᗮ) 1 → Kᗮ)
          (LogdetLean.uniformSphereSurfaceMeasure (E := Kᗮ))) := by
      rw [LogdetLean.map_unitDirection_stdGaussian_eq_uniformSphereSurfaceMeasure]
    _ = Measure.map
        (fun s : sphere (0 : Kᗮ) 1 ↦
          ((s.1 : Kᗮ) : EuclideanSpace ℂ (Fin M)))
        (LogdetLean.uniformSphereSurfaceMeasure (E := Kᗮ)) := by
      rw [Measure.map_map measurable_subtype_coe measurable_subtype_coe]
      rfl

/-! ## Ambient-unitary equivariance -/

/-- Left multiplication of a partial frame by an ambient unitary. -/
def h19StiefelUnitaryLeftAction {M L : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (Q : Matrix (Fin M) (Fin L) ℂ) : Matrix (Fin M) (Fin L) ℂ :=
  (U : Matrix (Fin M) (Fin M) ℂ) * Q

theorem h19StiefelComplementMatrix_unitaryLeftAction {M L : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (Q : Matrix (Fin M) (Fin L) ℂ) :
    h19StiefelComplementMatrix (h19StiefelUnitaryLeftAction U Q) =
      (U : Matrix (Fin M) (Fin M) ℂ) *
        h19StiefelComplementMatrix Q *
          (U : Matrix (Fin M) (Fin M) ℂ).conjTranspose := by
  change 1 - ((U : Matrix (Fin M) (Fin M) ℂ) * Q) *
      ((U : Matrix (Fin M) (Fin M) ℂ) * Q).conjTranspose = _
  rw [Matrix.conjTranspose_mul]
  have hU : (U : Matrix (Fin M) (Fin M) ℂ) *
      (U : Matrix (Fin M) (Fin M) ℂ).conjTranspose = 1 := by
    simpa [← Matrix.star_eq_conjTranspose] using
      (Unitary.coe_mul_star_self U)
  simp only [h19StiefelComplementMatrix, Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU]

theorem h19StiefelProjectedGaussian_unitary_equivariant {M L : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (g : EuclideanSpace ℂ (Fin M)) :
    h19StiefelProjectedGaussian (h19StiefelUnitaryLeftAction U Q)
        (h1UnitaryEuclideanRealIsometryEquiv U g) =
      h1UnitaryEuclideanRealIsometryEquiv U
        (h19StiefelProjectedGaussian Q g) := by
  apply WithLp.ofLp_injective 2
  change h19StiefelComplementMatrix (h19StiefelUnitaryLeftAction U Q) *ᵥ
      ((U : Matrix (Fin M) (Fin M) ℂ) *ᵥ WithLp.ofLp g) =
    (U : Matrix (Fin M) (Fin M) ℂ) *ᵥ
      (h19StiefelComplementMatrix Q *ᵥ WithLp.ofLp g)
  rw [h19StiefelComplementMatrix_unitaryLeftAction,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hU : (U : Matrix (Fin M) (Fin M) ℂ).conjTranspose *
      (U : Matrix (Fin M) (Fin M) ℂ) = 1 := by
    simpa [← Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self U)
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one]

theorem h19StiefelNextColumn_unitary_equivariant {M L : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (Q : Matrix (Fin M) (Fin L) ℂ)
    (g : EuclideanSpace ℂ (Fin M)) :
    h19StiefelNextColumn (h19StiefelUnitaryLeftAction U Q)
        (h1UnitaryEuclideanRealIsometryEquiv U g) =
      h1UnitaryEuclideanRealIsometryEquiv U
        (h19StiefelNextColumn Q g) := by
  rw [h19StiefelNextColumn, h19StiefelNextColumn,
    h19StiefelProjectedGaussian_unitary_equivariant]
  exact h1UnitDirection_h1UnitaryEuclideanRealIsometryEquiv U _

/-- Exact covariance of the fixed-frame candidate law under simultaneous
ambient-unitary rotation of the past frame and next column.  This is the
measure-level conditional-kernel identity furnished by the Gaussian
construction. -/
theorem map_h19StiefelNextColumnLaw_unitary_equivariant {M L : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (Q : Matrix (Fin M) (Fin L) ℂ) :
    Measure.map (h1UnitaryEuclideanRealIsometryEquiv U)
        (h19StiefelNextColumnLaw Q) =
      h19StiefelNextColumnLaw (h19StiefelUnitaryLeftAction U Q) := by
  let f := h1UnitaryEuclideanRealIsometryEquiv U
  calc
    Measure.map f (h19StiefelNextColumnLaw Q) =
        Measure.map (f ∘ h19StiefelNextColumn Q)
          (stdGaussian (EuclideanSpace ℂ (Fin M))) := by
      unfold h19StiefelNextColumnLaw
      rw [Measure.map_map f.continuous.measurable
        (measurable_h19StiefelNextColumn Q)]
    _ = Measure.map
        (h19StiefelNextColumn (h19StiefelUnitaryLeftAction U Q) ∘ f)
          (stdGaussian (EuclideanSpace ℂ (Fin M))) := by
      congr 1
      funext g
      exact (h19StiefelNextColumn_unitary_equivariant U Q g).symm
    _ = Measure.map
        (h19StiefelNextColumn (h19StiefelUnitaryLeftAction U Q))
        (Measure.map f (stdGaussian (EuclideanSpace ℂ (Fin M)))) := by
      rw [Measure.map_map
        (measurable_h19StiefelNextColumn
          (h19StiefelUnitaryLeftAction U Q))
        f.continuous.measurable]
    _ = h19StiefelNextColumnLaw
        (h19StiefelUnitaryLeftAction U Q) := by
      rw [ProbabilityTheory.stdGaussian_map f]
      rfl

/-! ## An exact joint Haar representation by suffix right invariance -/

/-- The first `L` columns of an ambient Haar unitary. -/
def h19HaarLeadingColumns {M L : ℕ} (hLM : L ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Matrix (Fin M) (Fin L) ℂ :=
  fun i j ↦ (U : Matrix (Fin M) (Fin M) ℂ) i (Fin.castLE hLM j)

/-- The remaining `M-L` columns of an ambient unitary. -/
def h19HaarSuffixColumns {M L : ℕ} (hLM : L ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Matrix (Fin M) (Fin (M - L)) ℂ :=
  fun i j ↦ (U : Matrix (Fin M) (Fin M) ℂ) i
    (haarAmbientPrefixEquiv hLM (Sum.inr j))

/-- We expose the last column of the remaining suffix.  Iterating this
choice backwards is equivalent to the usual next-column recursion and lets
us reuse the axiom-free H1 last-column sphere theorem literally. -/
def h19HaarSuffixLastColumn {M L : ℕ} (hLM : L ≤ M)
    (hrem : 1 ≤ M - L) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 (fun i ↦
    (U : Matrix (Fin M) (Fin M) ℂ) i
      (haarAmbientPrefixEquiv hLM
        (Sum.inr (haarLastColumnIndex hrem))))

/-- Apply the suffix frame to the last-column direction of an independent
Haar unitary on the remaining coordinates. -/
def h19HaarSuffixFrameTimesLastColumn {M L : ℕ} (hLM : L ≤ M)
    (hrem : 1 ≤ M - L)
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
    EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2
    (h19HaarSuffixColumns hLM U *ᵥ
      WithLp.ofLp (haarLastColumnSphere hrem V).1)

/-- The suffix frame applied directly to a sphere direction. -/
def h19HaarSuffixFrameTimesSphere {M L : ℕ} (hLM : L ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (s : ComplexUnitSphere (M - L)) :
    EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2
    (h19HaarSuffixColumns hLM U *ᵥ WithLp.ofLp s.1)

theorem measurable_h19HaarLeadingColumns {M L : ℕ} (hLM : L ≤ M) :
    Measurable (h19HaarLeadingColumns hLM) := by
  unfold h19HaarLeadingColumns
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact (measurable_pi_apply (Fin.castLE hLM j)).comp
    ((measurable_pi_apply i).comp measurable_subtype_coe)

theorem measurable_h19HaarSuffixLastColumn {M L : ℕ}
    (hLM : L ≤ M) (hrem : 1 ≤ M - L) :
    Measurable (h19HaarSuffixLastColumn hLM hrem) := by
  unfold h19HaarSuffixLastColumn
  apply (WithLp.measurable_toLp 2 (Fin M → ℂ)).comp
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (measurable_pi_apply
      (haarAmbientPrefixEquiv hLM
        (Sum.inr (haarLastColumnIndex hrem)))).comp
    ((measurable_pi_apply i).comp measurable_subtype_coe)

theorem measurable_h19HaarSuffixFrameTimesLastColumn_uncurry {M L : ℕ}
    (hLM : L ≤ M) (hrem : 1 ≤ M - L) :
    Measurable (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
        Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
      h19HaarSuffixFrameTimesLastColumn hLM hrem p.1 p.2) := by
  unfold h19HaarSuffixFrameTimesLastColumn h19HaarSuffixColumns
  apply (WithLp.measurable_toLp 2 (Fin M → ℂ)).comp
  refine measurable_pi_lambda _ fun i ↦ ?_
  change Measurable (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
    ∑ j : Fin (M - L),
      (p.1 : Matrix (Fin M) (Fin M) ℂ) i
          (haarAmbientPrefixEquiv hLM (Sum.inr j)) *
        (haarLastColumnSphere hrem p.2).1 j)
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  have hleft : Measurable (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
      (p.1 : Matrix (Fin M) (Fin M) ℂ) i
        (haarAmbientPrefixEquiv hLM (Sum.inr j))) :=
    (measurable_pi_apply (haarAmbientPrefixEquiv hLM (Sum.inr j))).comp
      ((measurable_pi_apply i).comp
        (measurable_subtype_coe.comp measurable_fst))
  have hright : Measurable (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
      (haarLastColumnSphere hrem p.2).1 j) :=
    (measurable_pi_apply j).comp
      ((WithLp.measurable_ofLp 2 (Fin (M - L) → ℂ)).comp
        (measurable_subtype_coe.comp
          ((measurable_haarLastColumnSphere hrem).comp measurable_snd)))
  exact hleft.mul hright

theorem measurable_h19HaarSuffixFrameTimesSphere_uncurry {M L : ℕ}
    (hLM : L ≤ M) :
    Measurable (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
        ComplexUnitSphere (M - L) ↦
      h19HaarSuffixFrameTimesSphere hLM p.1 p.2) := by
  unfold h19HaarSuffixFrameTimesSphere h19HaarSuffixColumns
  apply (WithLp.measurable_toLp 2 (Fin M → ℂ)).comp
  refine measurable_pi_lambda _ fun i ↦ ?_
  change Measurable (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      ComplexUnitSphere (M - L) ↦
    ∑ j : Fin (M - L),
      (p.1 : Matrix (Fin M) (Fin M) ℂ) i
          (haarAmbientPrefixEquiv hLM (Sum.inr j)) * p.2.1 j)
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  have hleft : Measurable (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      ComplexUnitSphere (M - L) ↦
      (p.1 : Matrix (Fin M) (Fin M) ℂ) i
        (haarAmbientPrefixEquiv hLM (Sum.inr j))) :=
    (measurable_pi_apply (haarAmbientPrefixEquiv hLM (Sum.inr j))).comp
      ((measurable_pi_apply i).comp
        (measurable_subtype_coe.comp measurable_fst))
  have hright : Measurable (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      ComplexUnitSphere (M - L) ↦ p.2.1 j) :=
    (measurable_pi_apply j).comp
      ((WithLp.measurable_ofLp 2 (Fin (M - L) → ℂ)).comp
        (measurable_subtype_coe.comp measurable_snd))
  exact hleft.mul hright

/-- A suffix right rotation fixes the observed leading frame pointwise. -/
theorem h19HaarLeadingColumns_mul_suffix {M L : ℕ}
    (hLM : L ≤ M) (U : Matrix.unitaryGroup (Fin M) ℂ)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
    h19HaarLeadingColumns hLM
        (U * h19HaarAmbientSuffixUnitary hLM V) =
      h19HaarLeadingColumns hLM U := by
  ext i j
  exact mul_h19HaarAmbientSuffixUnitary_apply_leading hLM U V i j

/-- The exposed suffix column after a suffix right rotation is the suffix
frame applied to the corresponding Haar last-column direction. -/
theorem h19HaarSuffixLastColumn_mul_suffix {M L : ℕ}
    (hLM : L ≤ M) (hrem : 1 ≤ M - L)
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
    h19HaarSuffixLastColumn hLM hrem
        (U * h19HaarAmbientSuffixUnitary hLM V) =
      h19HaarSuffixFrameTimesLastColumn hLM hrem U V := by
  apply WithLp.ofLp_injective 2
  ext i
  change (∑ k : Fin M,
      (U : Matrix (Fin M) (Fin M) ℂ) i k *
        (h19HaarAmbientSuffixUnitary hLM V :
          Matrix (Fin M) (Fin M) ℂ) k
          (haarAmbientPrefixEquiv hLM
            (Sum.inr (haarLastColumnIndex hrem)))) = _
  let e := haarAmbientPrefixEquiv hLM
  rw [← Fintype.sum_equiv e
    (fun k : Fin L ⊕ Fin (M - L) ↦
      (U : Matrix (Fin M) (Fin M) ℂ) i (e k) *
        (h19HaarAmbientSuffixUnitary hLM V :
          Matrix (Fin M) (Fin M) ℂ) (e k)
          (e (Sum.inr (haarLastColumnIndex hrem))))
    (fun k : Fin M ↦
      (U : Matrix (Fin M) (Fin M) ℂ) i k *
        (h19HaarAmbientSuffixUnitary hLM V :
          Matrix (Fin M) (Fin M) ℂ) k
          (e (Sum.inr (haarLastColumnIndex hrem))))
    (fun _ ↦ rfl)]
  rw [Fintype.sum_sum_type]
  simp [e, h19HaarSuffixFrameTimesLastColumn,
    h19HaarSuffixColumns, Matrix.mulVec, dotProduct,
    haarLastColumnSphere_apply]

/-- Exact joint-law representation.  The leading `L` columns and one
remaining column of an ambient Haar unitary have the same joint law as the
same leading frame together with its suffix frame applied to an independent
uniform complex-sphere direction of dimension `M-L`. -/
theorem map_haar_leadingColumns_suffixLastColumn_eq_independentSphereFrame
    {M L : ℕ} (hLM : L ≤ M) (hrem : 1 ≤ M - L) :
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
          (h19HaarLeadingColumns hLM U,
            h19HaarSuffixLastColumn hLM hrem U))
        (unitaryHaarProbabilityMeasure M) =
      Measure.map
        (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
            Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
          (h19HaarLeadingColumns hLM p.1,
            h19HaarSuffixFrameTimesLastColumn hLM hrem p.1 p.2))
        ((unitaryHaarProbabilityMeasure M).prod
          (unitaryHaarProbabilityMeasure (M - L))) := by
  let rotate := fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
        p.1 * h19HaarAmbientSuffixUnitary hLM p.2
  let observe := fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
    (h19HaarLeadingColumns hLM U,
      h19HaarSuffixLastColumn hLM hrem U)
  have hrotate : Measurable rotate :=
    measurable_mul_h19HaarAmbientSuffixUnitary_uncurry hLM
  have hobserve : Measurable observe :=
    (measurable_h19HaarLeadingColumns hLM).prodMk
      (measurable_h19HaarSuffixLastColumn hLM hrem)
  let μprod := (unitaryHaarProbabilityMeasure M).prod
    (unitaryHaarProbabilityMeasure (M - L))
  have hrotmap : Measure.map rotate μprod =
      unitaryHaarProbabilityMeasure M :=
    map_mul_h19HaarAmbientSuffixUnitary_prod_haar hLM
  calc
    Measure.map observe (unitaryHaarProbabilityMeasure M) =
        Measure.map observe (Measure.map rotate μprod) := by rw [hrotmap]
    _ = Measure.map (observe ∘ rotate) μprod := by
      rw [Measure.map_map hobserve hrotate]
    _ = Measure.map
        (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
            Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
          (h19HaarLeadingColumns hLM p.1,
            h19HaarSuffixFrameTimesLastColumn hLM hrem p.1 p.2))
        μprod := by
      apply Measure.map_congr
      filter_upwards [] with p
      apply Prod.ext
      · exact h19HaarLeadingColumns_mul_suffix hLM p.1 p.2
      · exact h19HaarSuffixLastColumn_mul_suffix hLM hrem p.1 p.2

/-- Sphere-valued form of the preceding joint law.  Here the second input
is literally independent normalized surface measure on the complex sphere
of dimension `M-L`, rather than a redundant full suffix Haar unitary. -/
theorem map_haar_leadingColumns_suffixLastColumn_eq_independentUniformSphere
    {M L : ℕ} (hLM : L ≤ M) (hrem : 1 ≤ M - L) :
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
          (h19HaarLeadingColumns hLM U,
            h19HaarSuffixLastColumn hLM hrem U))
        (unitaryHaarProbabilityMeasure M) =
      Measure.map
        (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
            ComplexUnitSphere (M - L) ↦
          (h19HaarLeadingColumns hLM p.1,
            h19HaarSuffixFrameTimesSphere hLM p.1 p.2))
        ((unitaryHaarProbabilityMeasure M).prod
          (complexUnitSphereProbabilityMeasure (M - L))) := by
  let μ := unitaryHaarProbabilityMeasure M
  let ν := unitaryHaarProbabilityMeasure (M - L)
  let σ := complexUnitSphereProbabilityMeasure (M - L)
  let F := fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
    (p.1, haarLastColumnSphere hrem p.2)
  let G := fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      ComplexUnitSphere (M - L) ↦
    (h19HaarLeadingColumns hLM p.1,
      h19HaarSuffixFrameTimesSphere hLM p.1 p.2)
  have hF : Measurable F :=
    measurable_fst.prodMk
      ((measurable_haarLastColumnSphere hrem).comp measurable_snd)
  have hG : Measurable G :=
    ((measurable_h19HaarLeadingColumns hLM).comp measurable_fst).prodMk
      (measurable_h19HaarSuffixFrameTimesSphere_uncurry hLM)
  have hFmap : Measure.map F (μ.prod ν) = μ.prod σ := by
    calc
      Measure.map F (μ.prod ν) = Measure.map
          (Prod.map id (haarLastColumnSphere hrem)) (μ.prod ν) := by
        apply Measure.map_congr
        filter_upwards [] with p
        rfl
      _ =
          (Measure.map id μ).prod
            (Measure.map (haarLastColumnSphere hrem) ν) := by
        exact (Measure.map_prod_map μ ν measurable_id
          (measurable_haarLastColumnSphere hrem)).symm
      _ = μ.prod σ := by
        rw [Measure.map_id,
          map_haarLastColumnSphere_unitaryHaarProbabilityMeasure hrem]
  calc
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
          (h19HaarLeadingColumns hLM U,
            h19HaarSuffixLastColumn hLM hrem U)) μ =
        Measure.map
          (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
              Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
            (h19HaarLeadingColumns hLM p.1,
              h19HaarSuffixFrameTimesLastColumn hLM hrem p.1 p.2))
          (μ.prod ν) :=
      map_haar_leadingColumns_suffixLastColumn_eq_independentSphereFrame
        hLM hrem
    _ = Measure.map (G ∘ F) (μ.prod ν) := by
      congr 1
    _ = Measure.map G (Measure.map F (μ.prod ν)) := by
      rw [Measure.map_map hG hF]
    _ = Measure.map G (μ.prod σ) := by rw [hFmap]

/-! ## Canonical square-root form of the conditional top-column law -/

/-- The canonical rectangular factor `[sqrt(I-AAᴴ), 0]`. -/
def h19ZeroPaddedDefectSqrt {K L d : ℕ} (hKd : K ≤ d)
    (A : Matrix (Fin K) (Fin L) ℂ) : Matrix (Fin K) (Fin d) ℂ :=
  fun i j ↦
    match (haarAmbientPrefixEquiv hKd).symm j with
    | Sum.inl q => haarCornerDefectSqrt A i q
    | Sum.inr _ => 0

theorem haarAmbientPrefixEquiv_symm_castLE_h19NextColumn
    {K d : ℕ} (hKd : K ≤ d) (j : Fin K) :
    (haarAmbientPrefixEquiv hKd).symm (Fin.castLE hKd j) = Sum.inl j := by
  apply (haarAmbientPrefixEquiv hKd).injective
  simp

@[simp]
theorem h19ZeroPaddedDefectSqrt_apply_prefix {K L d : ℕ}
    (hKd : K ≤ d) (A : Matrix (Fin K) (Fin L) ℂ)
    (i j : Fin K) :
    h19ZeroPaddedDefectSqrt hKd A i (Fin.castLE hKd j) =
      haarCornerDefectSqrt A i j := by
  unfold h19ZeroPaddedDefectSqrt
  rw [haarAmbientPrefixEquiv_symm_castLE_h19NextColumn]

/-- The first `K` coordinates of a vector in ambient dimension `d`. -/
def h19TopCoordinates {K d : ℕ} (hKd : K ≤ d)
    (v : Fin d → ℂ) : Fin K → ℂ :=
  fun j ↦ v (Fin.castLE hKd j)

theorem h19ZeroPaddedDefectSqrt_mulVec {K L d : ℕ}
    (hKd : K ≤ d) (A : Matrix (Fin K) (Fin L) ℂ)
    (v : Fin d → ℂ) :
    h19ZeroPaddedDefectSqrt hKd A *ᵥ v =
      haarCornerDefectSqrt A *ᵥ h19TopCoordinates hKd v := by
  ext i
  unfold Matrix.mulVec dotProduct h19TopCoordinates
  let e := haarAmbientPrefixEquiv hKd
  rw [← Fintype.sum_equiv e
    (fun a : Fin K ⊕ Fin (d - K) ↦
      h19ZeroPaddedDefectSqrt hKd A i (e a) * v (e a))
    (fun j : Fin d ↦ h19ZeroPaddedDefectSqrt hKd A i j * v j)
    (fun _ ↦ rfl), Fintype.sum_sum_type]
  simp [e, h19ZeroPaddedDefectSqrt,
    haarAmbientPrefixEquiv_symm_castLE_h19NextColumn]

theorem h19ZeroPaddedDefectSqrt_mul_conjTranspose {K L d : ℕ}
    (hKd : K ≤ d) (A : Matrix (Fin K) (Fin L) ℂ) :
    h19ZeroPaddedDefectSqrt hKd A *
        (h19ZeroPaddedDefectSqrt hKd A).conjTranspose =
      haarCornerDefectSqrt A * (haarCornerDefectSqrt A).conjTranspose := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  let e := haarAmbientPrefixEquiv hKd
  rw [← Fintype.sum_equiv e
    (fun a : Fin K ⊕ Fin (d - K) ↦
      h19ZeroPaddedDefectSqrt hKd A i (e a) *
        star (h19ZeroPaddedDefectSqrt hKd A j (e a)))
    (fun q : Fin d ↦ h19ZeroPaddedDefectSqrt hKd A i q *
      star (h19ZeroPaddedDefectSqrt hKd A j q))
    (fun _ ↦ rfl), Fintype.sum_sum_type]
  simp [e, h19ZeroPaddedDefectSqrt,
    haarAmbientPrefixEquiv_symm_castLE_h19NextColumn]

/-- The canonical zero-padded square root has the same row Gram as the
unobserved top suffix block. -/
theorem h19CanonicalDefectFactor_mul_conjTranspose
    {M K L : ℕ} (hKM : K ≤ M) (hLM : L ≤ M)
    (hKd : K ≤ M - L) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    h19ZeroPaddedDefectSqrt hKd (h19HaarTallPast hKM hLM U) *
        (h19ZeroPaddedDefectSqrt hKd
          (h19HaarTallPast hKM hLM U)).conjTranspose =
      haarCornerLeftDefect (h19HaarTallPast hKM hLM U) := by
  rw [h19ZeroPaddedDefectSqrt_mul_conjTranspose,
    (haarCornerDefectSqrt_isHermitian
      (h19HaarTallPast hKM hLM U)).eq]
  apply CFC.sqrt_mul_sqrt_self
  have hpsd :
      (haarCornerLeftDefect (h19HaarTallPast hKM hLM U)).PosSemidef := by
    rw [← h19HaarTopSuffix_mul_conjTranspose hKM hLM U]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  exact hpsd.nonneg

/-- Equal row Grams put the actual suffix block and canonical square-root
factor in the same right-unitary orbit, including singular fibers. -/
theorem exists_h19HaarTopSuffix_rightUnitary_eq_zeroPaddedDefectSqrt
    {M K L : ℕ} (hKM : K ≤ M) (hLM : L ≤ M)
    (hKd : K ≤ M - L) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    ∃ W : Matrix.unitaryGroup (Fin (M - L)) ℂ,
      h19HaarTopSuffix hKM hLM U *
          (W : Matrix (Fin (M - L)) (Fin (M - L)) ℂ) =
        h19ZeroPaddedDefectSqrt hKd (h19HaarTallPast hKM hLM U) := by
  apply exists_rightUnitary_of_hermitianRowGram_eq
  rw [h19HaarTopSuffix_mul_conjTranspose hKM hLM U,
    h19CanonicalDefectFactor_mul_conjTranspose hKM hLM hKd U]

theorem h19HaarSuffixFirstColumn_mul_left {d : ℕ} (hd : 0 < d)
    (W V : Matrix.unitaryGroup (Fin d) ℂ) :
    h19HaarSuffixFirstColumn hd (W * V) =
      (W : Matrix (Fin d) (Fin d) ℂ) *ᵥ
        h19HaarSuffixFirstColumn hd V := by
  ext i
  simp [h19HaarSuffixFirstColumn, Matrix.mul_apply, Matrix.mulVec,
    dotProduct]

/-- The first standard coordinate as a point of the complex unit sphere. -/
def h19HaarFirstColumnBaseSphere {d : ℕ} (hd : 0 < d) :
    ComplexUnitSphere d :=
  ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℂ), by
    rw [mem_sphere_zero_iff_norm]
    simp⟩

/-- The first column of a unitary, as a sphere-valued random variable. -/
def h19HaarSuffixFirstColumnSphere {d : ℕ} (hd : 0 < d) :
    Matrix.unitaryGroup (Fin d) ℂ → ComplexUnitSphere d :=
  fun V ↦ h1UnitarySphereAction V (h19HaarFirstColumnBaseSphere hd)

@[simp]
theorem h19HaarSuffixFirstColumnSphere_val {d : ℕ} (hd : 0 < d)
    (V : Matrix.unitaryGroup (Fin d) ℂ) :
    WithLp.ofLp (h19HaarSuffixFirstColumnSphere hd V).1 =
      h19HaarSuffixFirstColumn hd V := by
  ext i
  simp [h19HaarSuffixFirstColumnSphere, h1UnitarySphereAction_val,
    h19HaarFirstColumnBaseSphere, h19HaarSuffixFirstColumn,
    Matrix.mulVec, dotProduct]

theorem measurable_h19HaarSuffixFirstColumnSphere {d : ℕ} (hd : 0 < d) :
    Measurable (h19HaarSuffixFirstColumnSphere hd) := by
  apply Measurable.subtype_mk
  have hraw : Measurable
      (fun V : Matrix.unitaryGroup (Fin d) ℂ ↦
        WithLp.toLp 2 (h19HaarSuffixFirstColumn hd V)) :=
    (WithLp.measurable_toLp 2 (Fin d → ℂ)).comp
      (measurable_h19HaarSuffixFirstColumn hd)
  convert hraw using 1
  funext V
  apply WithLp.ofLp_injective 2
  exact h19HaarSuffixFirstColumnSphere_val hd V

theorem measurable_unitary_mul_left_h19NextColumn {d : ℕ}
    (W : Matrix.unitaryGroup (Fin d) ℂ) :
    Measurable (fun V : Matrix.unitaryGroup (Fin d) ℂ ↦ W * V) := by
  apply Measurable.subtype_mk
  change Measurable
    (fun V : Matrix.unitaryGroup (Fin d) ℂ ↦
      (W : Matrix (Fin d) (Fin d) ℂ) *
        (V : Matrix (Fin d) (Fin d) ℂ))
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ ↦ ?_
  exact measurable_const.mul
    ((measurable_pi_apply j).comp
      ((measurable_pi_apply k).comp measurable_subtype_coe))

theorem measurable_unitary_mul_right_h19NextColumn {d : ℕ}
    (W : Matrix.unitaryGroup (Fin d) ℂ) :
    Measurable (fun V : Matrix.unitaryGroup (Fin d) ℂ ↦ V * W) := by
  apply Measurable.subtype_mk
  change Measurable
    (fun V : Matrix.unitaryGroup (Fin d) ℂ ↦
      (V : Matrix (Fin d) (Fin d) ℂ) *
        (W : Matrix (Fin d) (Fin d) ℂ))
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ ↦ ?_
  have hcoe : Measurable
      (fun V : Matrix.unitaryGroup (Fin d) ℂ ↦
        (V : Matrix (Fin d) (Fin d) ℂ)) := measurable_subtype_coe
  exact ((measurable_pi_apply k).comp
      ((measurable_pi_apply i).comp hcoe)).mul measurable_const

/-- The first column of a normalized Haar unitary is uniform on the complex
unit sphere.  This is transported from the already-proved last-column law. -/
theorem map_h19HaarSuffixFirstColumnSphere {d : ℕ} (hd : 0 < d) :
    Measure.map (h19HaarSuffixFirstColumnSphere hd)
        (unitaryHaarProbabilityMeasure d) =
      complexUnitSphereProbabilityMeasure d := by
  obtain ⟨P, hP⟩ := exists_unitary_lastColumn_eq hd
    (h19HaarFirstColumnBaseSphere hd)
  let μ := unitaryHaarProbabilityMeasure d
  have hlast : Measurable (haarLastColumnSphere hd) :=
    measurable_haarLastColumnSphere hd
  have hright : Measurable
      (fun V : Matrix.unitaryGroup (Fin d) ℂ ↦ V * P) :=
    measurable_unitary_mul_right_h19NextColumn P
  have hpoint (V : Matrix.unitaryGroup (Fin d) ℂ) :
      h19HaarSuffixFirstColumnSphere hd V =
        haarLastColumnSphere hd (V * P) := by
    unfold h19HaarSuffixFirstColumnSphere
    rw [← hP]
    change h1UnitarySphereAction V
        (h1UnitarySphereAction P (haarLastColumnBaseSphere hd)) =
      h1UnitarySphereAction (V * P) (haarLastColumnBaseSphere hd)
    exact unitarySphereAction_comp V P (haarLastColumnBaseSphere hd)
  calc
    Measure.map (h19HaarSuffixFirstColumnSphere hd) μ =
        Measure.map (haarLastColumnSphere hd ∘ fun V ↦ V * P) μ := by
      apply Measure.map_congr
      filter_upwards [] with V
      exact hpoint V
    _ = Measure.map (haarLastColumnSphere hd)
        (Measure.map (fun V ↦ V * P) μ) := by
      rw [Measure.map_map hlast hright]
    _ = Measure.map (haarLastColumnSphere hd) μ := by
      rw [map_unitaryHaarProbabilityMeasure_mul_right_h1 d P]
    _ = complexUnitSphereProbabilityMeasure d :=
      map_haarLastColumnSphere_unitaryHaarProbabilityMeasure hd

/-- The square-root construction driven by the first column of an
independent suffix Haar unitary. -/
def h19CanonicalGeneratedTopColumn {M K L : ℕ}
    (hKM : K ≤ M) (hLM : L ≤ M) (hKd : K ≤ M - L)
    (hd : 0 < M - L) (U : Matrix.unitaryGroup (Fin M) ℂ)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) : Fin K → ℂ :=
  haarCornerDefectSqrt (h19HaarTallPast hKM hLM U) *ᵥ
    h19TopCoordinates hKd (h19HaarSuffixFirstColumn hd V)

/-- The same square-root construction driven directly by a uniform sphere
direction of complex dimension `M-L`. -/
def h19CanonicalSphereGeneratedTopColumn {M K L : ℕ}
    (hKM : K ≤ M) (hLM : L ≤ M) (hKd : K ≤ M - L)
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (s : ComplexUnitSphere (M - L)) : Fin K → ℂ :=
  haarCornerDefectSqrt (h19HaarTallPast hKM hLM U) *ᵥ
    h19TopCoordinates hKd (WithLp.ofLp s.1)

theorem measurable_h19CanonicalSphereGeneratedTopColumn
    {M K L : ℕ} (hKM : K ≤ M) (hLM : L ≤ M)
    (hKd : K ≤ M - L) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Measurable (h19CanonicalSphereGeneratedTopColumn hKM hLM hKd U) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  unfold h19CanonicalSphereGeneratedTopColumn Matrix.mulVec dotProduct
    h19TopCoordinates
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  exact measurable_const.mul
    ((measurable_pi_apply (Fin.castLE hKd j)).comp
      ((WithLp.measurable_ofLp 2 (Fin (M - L) → ℂ)).comp
        measurable_subtype_coe))

theorem map_h19CanonicalGeneratedTopColumn_eq_sphere
    {M K L : ℕ} (hKM : K ≤ M) (hLM : L ≤ M)
    (hKd : K ≤ M - L) (hd : 0 < M - L)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Measure.map (h19CanonicalGeneratedTopColumn hKM hLM hKd hd U)
        (unitaryHaarProbabilityMeasure (M - L)) =
      Measure.map
        (h19CanonicalSphereGeneratedTopColumn hKM hLM hKd U)
        (complexUnitSphereProbabilityMeasure (M - L)) := by
  let μ := unitaryHaarProbabilityMeasure (M - L)
  let σ := complexUnitSphereProbabilityMeasure (M - L)
  let F := h19HaarSuffixFirstColumnSphere hd
  let G := h19CanonicalSphereGeneratedTopColumn hKM hLM hKd U
  have hF : Measurable F := measurable_h19HaarSuffixFirstColumnSphere hd
  have hG : Measurable G :=
    measurable_h19CanonicalSphereGeneratedTopColumn hKM hLM hKd U
  have hpoint (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
      h19CanonicalGeneratedTopColumn hKM hLM hKd hd U V = G (F V) := by
    unfold h19CanonicalGeneratedTopColumn G
      h19CanonicalSphereGeneratedTopColumn F
    rw [h19HaarSuffixFirstColumnSphere_val]
  calc
    Measure.map (h19CanonicalGeneratedTopColumn hKM hLM hKd hd U) μ =
        Measure.map (G ∘ F) μ := by
      apply Measure.map_congr
      filter_upwards [] with V
      exact hpoint V
    _ = Measure.map G (Measure.map F μ) := by
      rw [Measure.map_map hG hF]
    _ = Measure.map G σ := by
      rw [map_h19HaarSuffixFirstColumnSphere hd]

/-- For every fixed past Haar frame, the actual suffix-generated top column
has exactly the canonical square-root law. -/
theorem map_h19HaarGeneratedTopColumn_eq_canonicalDefectSqrt
    {M K L : ℕ} (hKM : K ≤ M) (hLM : L ≤ M)
    (hKd : K ≤ M - L) (hd : 0 < M - L)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Measure.map
        (fun V : Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
          h19HaarGeneratedTopColumn hKM hLM hd (U, V))
        (unitaryHaarProbabilityMeasure (M - L)) =
      Measure.map
        (h19CanonicalGeneratedTopColumn hKM hLM hKd hd U)
        (unitaryHaarProbabilityMeasure (M - L)) := by
  letI : Measure.IsHaarMeasure
      (unitaryHaarProbabilityMeasure (M - L)) :=
    canonicalUnitaryHaarProbabilityFamily.isHaar (M - L)
  obtain ⟨W, hW⟩ :=
    exists_h19HaarTopSuffix_rightUnitary_eq_zeroPaddedDefectSqrt
      hKM hLM hKd U
  let f := fun V : Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
    h19HaarGeneratedTopColumn hKM hLM hd (U, V)
  let c := h19CanonicalGeneratedTopColumn hKM hLM hKd hd U
  have hf : Measurable f :=
    (measurable_h19HaarGeneratedTopColumn hKM hLM hd).comp
      (measurable_const.prodMk measurable_id)
  have hleft : Measurable
      (fun V : Matrix.unitaryGroup (Fin (M - L)) ℂ ↦ W * V) :=
    measurable_unitary_mul_left_h19NextColumn W
  have hpoint (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
      c V = f (W * V) := by
    unfold c h19CanonicalGeneratedTopColumn f h19HaarGeneratedTopColumn
    rw [← h19ZeroPaddedDefectSqrt_mulVec hKd, ← hW]
    change
      (h19HaarTopSuffix hKM hLM U *
          (W : Matrix (Fin (M - L)) (Fin (M - L)) ℂ)) *ᵥ
          h19HaarSuffixFirstColumn hd V =
        h19HaarTopSuffix hKM hLM U *ᵥ
          h19HaarSuffixFirstColumn hd (W * V)
    rw [← Matrix.mulVec_mulVec, h19HaarSuffixFirstColumn_mul_left]
  symm
  calc
    Measure.map c (unitaryHaarProbabilityMeasure (M - L)) =
        Measure.map (f ∘ fun V ↦ W * V)
          (unitaryHaarProbabilityMeasure (M - L)) := by
      apply Measure.map_congr
      filter_upwards [] with V
      exact hpoint V
    _ = Measure.map f
        (Measure.map (fun V ↦ W * V)
          (unitaryHaarProbabilityMeasure (M - L))) := by
      rw [Measure.map_map hf hleft]
    _ = Measure.map f (unitaryHaarProbabilityMeasure (M - L)) := by
      rw [map_mul_left_eq_self (unitaryHaarProbabilityMeasure (M - L)) W]

/-- Final conditional-law form: the next top column is
`sqrt(I-AAᴴ)` times the first `K` coordinates of an independent uniform
complex-sphere direction of dimension `M-L`. -/
theorem map_h19HaarGeneratedTopColumn_eq_canonicalSphereDefectSqrt
    {M K L : ℕ} (hKM : K ≤ M) (hLM : L ≤ M)
    (hKd : K ≤ M - L) (hd : 0 < M - L)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Measure.map
        (fun V : Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
          h19HaarGeneratedTopColumn hKM hLM hd (U, V))
        (unitaryHaarProbabilityMeasure (M - L)) =
      Measure.map
        (h19CanonicalSphereGeneratedTopColumn hKM hLM hKd U)
        (complexUnitSphereProbabilityMeasure (M - L)) := by
  rw [map_h19HaarGeneratedTopColumn_eq_canonicalDefectSqrt
      hKM hLM hKd hd U,
    map_h19CanonicalGeneratedTopColumn_eq_sphere hKM hLM hKd hd U]

/-! ## Explicit density of the independent top-coordinate input -/

/-- The top `K` coordinates, packaged in the Euclidean-space type used by
the explicit one-column density. -/
def h19TopCoordinatesEuclidean {K d : ℕ} (hKd : K ≤ d)
    (s : ComplexUnitSphere d) : EuclideanSpace ℂ (Fin K) :=
  WithLp.toLp 2 (h19TopCoordinates hKd (WithLp.ofLp s.1))

/-- After the canonical equality `d = K + (d-K)`, the general
top-coordinate map is literally the H1 top-coordinate map. -/
theorem h19TopCoordinatesEuclidean_eq_h1TopCoordinates_sphereDimCast
    {K d : ℕ} (hKd : K ≤ d) (s : ComplexUnitSphere d) :
    h19TopCoordinatesEuclidean hKd s =
      h1TopCoordinates
        ((h1SphereDimCast (Nat.add_sub_of_le hKd).symm) s).1 := by
  apply WithLp.ofLp_injective 2
  ext i
  change (WithLp.ofLp s.1) (Fin.castLE hKd i) = _
  rw [h1TopCoordinates_sphereDimCast_apply]
  have hi : Fin.castLE hKd i =
      Fin.cast (Nat.add_sub_of_le hKd)
        (Fin.castAdd (d - K) i) := by
    apply Fin.ext
    rfl
  rw [hi]

theorem measurable_h19TopCoordinatesEuclidean
    {K d : ℕ} (hKd : K ≤ d) :
    Measurable (h19TopCoordinatesEuclidean hKd) := by
  unfold h19TopCoordinatesEuclidean h19TopCoordinates
  fun_prop

/-- Dimension-free version of the elementary top-coordinate sphere density:
for `1 ≤ K < d`, the first `K` complex coordinates of a uniform sphere
direction in dimension `d` have density `h19BaseColumnVectorPDF K (d-K)`. -/
theorem map_h19TopCoordinatesEuclidean_complexUnitSphere_withDensity
    {K d : ℕ} (hK : 1 ≤ K) (hKd : K < d) :
    Measure.map (h19TopCoordinatesEuclidean hKd.le)
        (complexUnitSphereProbabilityMeasure d) =
      (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K (d - K)) := by
  let r := d - K
  let e := h1SphereDimCast (Nat.add_sub_of_le hKd.le).symm
  let G := fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1
  have he : Measurable e := e.measurable
  have hG : Measurable G := by
    unfold G h1TopCoordinates
    fun_prop
  have hpoint (s : ComplexUnitSphere d) :
      h19TopCoordinatesEuclidean hKd.le s = G (e s) := by
    exact h19TopCoordinatesEuclidean_eq_h1TopCoordinates_sphereDimCast
      hKd.le s
  calc
    Measure.map (h19TopCoordinatesEuclidean hKd.le)
        (complexUnitSphereProbabilityMeasure d) =
      Measure.map (G ∘ e) (complexUnitSphereProbabilityMeasure d) := by
        apply Measure.map_congr
        filter_upwards [] with s
        exact hpoint s
    _ = Measure.map G
        (Measure.map e (complexUnitSphereProbabilityMeasure d)) := by
      rw [Measure.map_map hG he]
    _ = Measure.map G (complexUnitSphereProbabilityMeasure (K + r)) := by
      rw [map_h1SphereDimCast_uniform]
    _ = (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K r) := by
      exact map_h1TopCoordinates_complexUnitSphereProbabilityMeasure_withDensity
        hK (by dsimp [r]; omega)

theorem measurable_h19HaarDefectSqrtMulVec
    {M K L : ℕ} (hKM : K ≤ M) (hLM : L ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Measurable
      (fun x : EuclideanSpace ℂ (Fin K) ↦
        haarCornerDefectSqrt (h19HaarTallPast hKM hLM U) *ᵥ
          WithLp.ofLp x) := by
  fun_prop

/-- Fixed-past density form of the Haar next-column law.  The actual suffix
column is the positive defect square root applied to an explicit
Lebesgue-density input on the complex unit ball. -/
theorem map_h19HaarGeneratedTopColumn_eq_defectSqrt_baseColumnDensity
    {M K L : ℕ} (hKM : K ≤ M) (hLM : L ≤ M)
    (hK : 1 ≤ K) (hKd : K < M - L)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Measure.map
        (fun V : Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
          h19HaarGeneratedTopColumn hKM hLM (by omega) (U, V))
        (unitaryHaarProbabilityMeasure (M - L)) =
      Measure.map
        (fun x : EuclideanSpace ℂ (Fin K) ↦
          haarCornerDefectSqrt (h19HaarTallPast hKM hLM U) *ᵥ
            WithLp.ofLp x)
        ((volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
          (h19BaseColumnVectorPDF K ((M - L) - K))) := by
  let d := M - L
  let T := h19TopCoordinatesEuclidean hKd.le
  let F := fun x : EuclideanSpace ℂ (Fin K) ↦
    haarCornerDefectSqrt (h19HaarTallPast hKM hLM U) *ᵥ WithLp.ofLp x
  have hT : Measurable T := measurable_h19TopCoordinatesEuclidean hKd.le
  have hF : Measurable F := measurable_h19HaarDefectSqrtMulVec hKM hLM U
  have hpoint (s : ComplexUnitSphere d) :
      h19CanonicalSphereGeneratedTopColumn hKM hLM hKd.le U s = F (T s) := by
    rfl
  calc
    Measure.map
        (fun V : Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
          h19HaarGeneratedTopColumn hKM hLM (by omega) (U, V))
        (unitaryHaarProbabilityMeasure (M - L)) =
      Measure.map
        (h19CanonicalSphereGeneratedTopColumn hKM hLM hKd.le U)
        (complexUnitSphereProbabilityMeasure (M - L)) :=
      map_h19HaarGeneratedTopColumn_eq_canonicalSphereDefectSqrt
        hKM hLM hKd.le (by omega) U
    _ = Measure.map (F ∘ T) (complexUnitSphereProbabilityMeasure d) := by
      apply Measure.map_congr
      filter_upwards [] with s
      exact hpoint s
    _ = Measure.map F
        (Measure.map T (complexUnitSphereProbabilityMeasure d)) := by
      rw [Measure.map_map hF hT]
    _ = Measure.map F
        ((volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
          (h19BaseColumnVectorPDF K (d - K))) := by
      rw [map_h19TopCoordinatesEuclidean_complexUnitSphere_withDensity hK hKd]

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
