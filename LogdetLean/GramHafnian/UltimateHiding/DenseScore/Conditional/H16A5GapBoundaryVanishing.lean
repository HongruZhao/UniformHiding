import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16EuclideanCoordinateCore
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic

/-!
# R-H16E: determinant-gap vanishing on the exact COE-support frontier

This module proves only the boundary compatibility requested before the
zero-extension Lipschitz step.  The proof uses the literal COE denominator
`I - CᴴC`:

* its Euclidean-coordinate realization is continuous and Hermitian;
* positive definiteness is locally stable, proved quantitatively from a
  strictly positive spectral lower bound;
* a frontier point is a limit of positive-definite denominators, hence its
  denominator is positive semidefinite;
* because the support is open, that frontier denominator is not positive
  definite, so its determinant is zero.

No Gauss--Green input, endpoint statement, or additional scientific axiom is
used here.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Boundary compatibility of the literal determinant gap.  The proposition
is defined here because the active A1 route proves it directly and does not
need the alternative A5/A6 coarea-perimeter development. -/
def H16EucGapBoundaryVanishing (N : ℕ) : Prop :=
  ∀ y : H16EuclideanCoordinateSpace N,
    y ∈ frontier (h16EucSupport N) → h16EucGap N y = 0

/-- Coordinate reconstruction as a complex-linear map.  This is the same
literal map already used throughout H16, now bundled so finite-dimensional
continuity applies for the operator-norm topology on matrices. -/
def h16ComplexSymmetricMatrixLinearMap (N : ℕ) :
    ComplexSymmetricCoordinates N →ₗ[ℂ] ConcreteMatrixState N where
  toFun := complexSymmetricMatrixOfCoordinates
  map_add' := complexSymmetricMatrixOfCoordinates_add
  map_smul' := complexSymmetricMatrixOfCoordinates_smul

/-- The literal Hermitian COE denominator in Euclidean coordinates. -/
def h16EucCornerDenominator (N : ℕ)
    (y : H16EuclideanCoordinateSpace N) : ConcreteMatrixState N :=
  let C := complexSymmetricMatrixOfCoordinates
    ((h16CoordinateEuclideanEquiv N).symm y)
  1 - star C * C

theorem continuous_h16EucCornerDenominator (N : ℕ) :
    Continuous (h16EucCornerDenominator N) := by
  have hC : Continuous (fun y : H16EuclideanCoordinateSpace N ↦
      complexSymmetricMatrixOfCoordinates
        ((h16CoordinateEuclideanEquiv N).symm y)) := by
    exact (LinearMap.continuous_of_finiteDimensional
      (h16ComplexSymmetricMatrixLinearMap N)).comp
        (h16CoordinateEuclideanEquiv N).symm.continuous
  change Continuous (fun y : H16EuclideanCoordinateSpace N ↦
    (1 : ConcreteMatrixState N) -
      star (complexSymmetricMatrixOfCoordinates
          ((h16CoordinateEuclideanEquiv N).symm y)) *
        complexSymmetricMatrixOfCoordinates
          ((h16CoordinateEuclideanEquiv N).symm y))
  exact continuous_const.sub (hC.star.mul hC)

theorem h16EucCornerDenominator_isHermitian (N : ℕ)
    (y : H16EuclideanCoordinateSpace N) :
    (h16EucCornerDenominator N y).IsHermitian := by
  classical
  simp only [h16EucCornerDenominator, Matrix.star_eq_conjTranspose]
  exact Matrix.isHermitian_one.sub
    (Matrix.isHermitian_conjTranspose_mul_self _)

theorem mem_h16EucSupport_iff_posDef (N : ℕ)
    (y : H16EuclideanCoordinateSpace N) :
    y ∈ h16EucSupport N ↔ (h16EucCornerDenominator N y).PosDef := by
  simp [h16EucSupport, coeCornerSupport, h16EucCornerDenominator,
    Matrix.star_eq_conjTranspose]

/-- The exact COE support is open.  The nonempty-dimensional case uses a
strict spectral lower bound and the norm control on self-adjoint
perturbations; the zero-dimensional matrix case is handled literally. -/
theorem isOpen_h16EucSupport (N : ℕ) : IsOpen (h16EucSupport N) := by
  classical
  by_cases hN : N = 0
  · subst N
    have hs : h16EucSupport 0 = Set.univ := by
      ext y
      simp only [Set.mem_univ, iff_true]
      rw [mem_h16EucSupport_iff_posDef]
      have hden : h16EucCornerDenominator 0 y =
          (1 : ConcreteMatrixState 0) := Subsingleton.elim _ _
      rw [hden]
      exact Matrix.PosDef.one
    rw [hs]
    exact isOpen_univ
  · letI : NeZero N := ⟨hN⟩
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hA : (h16EucCornerDenominator N y).PosDef :=
      (mem_h16EucSupport_iff_posDef N y).mp hy
    have hstrict : IsStrictlyPositive (h16EucCornerDenominator N y) :=
      hA.isStrictlyPositive
    obtain ⟨r, hr, hrA⟩ : ∃ r > 0,
        algebraMap ℝ (ConcreteMatrixState N) r ≤
          h16EucCornerDenominator N y :=
      (CFC.exists_pos_algebraMap_le_iff hstrict.isSelfAdjoint).2
        (fun x hx ↦ hstrict.spectrum_pos hx)
    have hpre : h16EucCornerDenominator N ⁻¹'
        Metric.ball (h16EucCornerDenominator N y) r ∈ 𝓝 y :=
      (continuous_h16EucCornerDenominator N).continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hr)
    refine Filter.mem_of_superset hpre ?_
    intro z hz
    apply (mem_h16EucSupport_iff_posDef N z).mpr
    let A : ConcreteMatrixState N := h16EucCornerDenominator N y
    let B : ConcreteMatrixState N := h16EucCornerDenominator N z
    let D : ConcreteMatrixState N := B - A
    have hnorm : ‖D‖ < r := by
      change dist B A < r at hz
      simpa [D, dist_eq_norm] using hz
    have hDherm : D.IsHermitian := by
      dsimp only [D, A, B]
      exact (h16EucCornerDenominator_isHermitian N z).sub
        (h16EucCornerDenominator_isHermitian N y)
    have hDlower :
        -(algebraMap ℝ (ConcreteMatrixState N) ‖D‖) ≤ D :=
      hDherm.isSelfAdjoint.neg_algebraMap_norm_le_self
    have hsB : algebraMap ℝ (ConcreteMatrixState N) (r - ‖D‖) ≤ B := by
      calc
        algebraMap ℝ (ConcreteMatrixState N) (r - ‖D‖) =
            algebraMap ℝ (ConcreteMatrixState N) r +
              -(algebraMap ℝ (ConcreteMatrixState N) ‖D‖) := by
                rw [map_sub]
                rfl
        _ ≤ A + D := add_le_add hrA hDlower
        _ = B := by simp [D]
    have hBstrict : IsStrictlyPositive B :=
      IsStrictlyPositive.of_le
        (isStrictlyPositive_algebraMap (sub_pos.mpr hnorm)) hsB
    exact Matrix.isStrictlyPositive_iff_posDef.mp hBstrict

/-- The literal determinant gap vanishes on the exact support frontier. -/
theorem h16EucGap_boundaryVanishing (N : ℕ) :
    H16EucGapBoundaryVanishing N := by
  classical
  intro y hy
  have hopen : IsOpen (h16EucSupport N) := isOpen_h16EucSupport N
  have hynot : y ∉ h16EucSupport N := by
    intro hys
    exact Set.disjoint_left.1 (disjoint_frontier_iff_isOpen.mpr hopen) hy hys
  have hs_subset : h16EucSupport N ⊆
      h16EucCornerDenominator N ⁻¹'
        {A : ConcreteMatrixState N | 0 ≤ A} := by
    intro z hz
    exact ((mem_h16EucSupport_iff_posDef N z).mp hz).posSemidef.nonneg
  have hclosed : IsClosed
      (h16EucCornerDenominator N ⁻¹'
        {A : ConcreteMatrixState N | 0 ≤ A}) :=
    CStarAlgebra.isClosed_nonneg.preimage
      (continuous_h16EucCornerDenominator N)
  have hynonneg_mem : y ∈ h16EucCornerDenominator N ⁻¹'
      {A : ConcreteMatrixState N | 0 ≤ A} :=
    (closure_minimal hs_subset hclosed) (frontier_subset_closure hy)
  have hynonneg : 0 ≤ h16EucCornerDenominator N y := hynonneg_mem
  have hypsd : (h16EucCornerDenominator N y).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hynonneg
  have hynotpd : ¬(h16EucCornerDenominator N y).PosDef := by
    intro hypd
    exact hynot ((mem_h16EucSupport_iff_posDef N y).mpr hypd)
  have hdet : (h16EucCornerDenominator N y).det = 0 := by
    by_contra hne
    exact hynotpd ((hypsd.posDef_iff_det_ne_zero).mpr hne)
  have hre := congrArg Complex.re hdet
  simpa [h16EucGap, h16COECoordinateGapDeterminant,
    h16EucCornerDenominator, Matrix.star_eq_conjTranspose] using hre

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
