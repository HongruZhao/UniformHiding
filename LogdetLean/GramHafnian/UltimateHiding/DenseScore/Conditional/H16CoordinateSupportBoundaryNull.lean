import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.OrderTwoApiScratch
import Mathlib.Analysis.Convex.Measure
import Mathlib.Tactic

/-!
# Nullity of the exact COE coordinate-support frontier

The matrix ball `I - Cᴴ C > 0` is convex.  The finite-dimensional Haar
measure theorem for convex frontiers therefore shows that its coordinate
frontier has Lebesgue measure zero.  This is the a.e. boundary input needed
for the sharp direct `3 -> 4` difference quotient.
-/

open MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.H3H4Central

/-- The exact positive-definite matrix ball is convex in the independent
complex-symmetric coordinates. -/
theorem convex_h16COECoordinateSupport {N : ℕ} (hN : 1 ≤ N) :
    Convex ℝ {x : ComplexSymmetricCoordinates N |
      coeCornerSupport (complexSymmetricMatrixOfCoordinates x)} := by
  let L := complexSymmetricMatrixOfCoordinatesLinearMapScratch N
  have hpreimage :
      {x : ComplexSymmetricCoordinates N |
          coeCornerSupport (complexSymmetricMatrixOfCoordinates x)} =
        L ⁻¹' Metric.ball (0 : ConcreteMatrixState N) 1 := by
    ext x
    change coeCornerSupport (complexSymmetricMatrixOfCoordinates x) ↔
      dist (L x) 0 < 1
    rw [coeCornerSupport_iff_cstar_norm_lt_one_scratch hN]
    rw [dist_zero_right]
    change ‖complexSymmetricMatrixOfCoordinates x‖ < 1 ↔
      ‖complexSymmetricMatrixOfCoordinates x‖ < 1
    rfl
  rw [hpreimage]
  exact (convex_ball (0 : ConcreteMatrixState N) 1).linear_preimage L

/-- The frontier of the base coordinate support is null for the exact
coordinate Lebesgue measure. -/
theorem measure_h16COECoordinateSupport_frontier_zero {N : ℕ} (hN : 1 ≤ N) :
    complexSymmetricCoordinateVolume N
      (frontier {x : ComplexSymmetricCoordinates N |
        coeCornerSupport (complexSymmetricMatrixOfCoordinates x)}) = 0 := by
  rw [show complexSymmetricCoordinateVolume N =
      (volume : Measure (ComplexSymmetricCoordinates N)) by
    unfold complexSymmetricCoordinateVolume
    exact MeasureTheory.volume_pi.symm]
  exact (convex_h16COECoordinateSupport hN).addHaar_frontier volume

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
