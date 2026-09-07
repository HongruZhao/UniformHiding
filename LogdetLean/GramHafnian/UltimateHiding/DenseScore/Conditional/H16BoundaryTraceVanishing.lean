import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16BoundaryExponentFour

/-!
# H16 boundary-flux vanishing from the sharp scalar estimate

This module isolates the complete scalar-to-limit step in the direct
integration-by-parts argument.  Its premise is only the determinant-specific
surface-flux bound; that bound, rather than any pointwise fourth derivative,
is the remaining geometric input.
-/

open Filter
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

theorem h16_boundary_trace_tendsto_zero_of_bound
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) (s : Fin 4)
    (F : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ‖F epsilon‖ ≤ C * epsilon ^
        (coeCornerDensityExponent N K - ((s : ℕ) : ℝ))) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun epsilon ↦ norm_nonneg (F epsilon)
  · exact hbound
  · simpa only [mul_zero] using
      (coe_boundary_rpow_tendsto_zero hboundary s).const_mul C

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
