import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFlowGeometry
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.QuadraticCenteringFromMass

/-!
# Time shift for one literal centered COE direction

The centered transpose-congruence maps form an additive flow.  Therefore an
arbitrary-time derivative of a fixed-direction event path is an origin
derivative for a measurable preimage event.  This is deterministic
measure/flow algebra; it uses no density, score, moment, TV, or hiding input.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The fixed-direction centered event path obeys the exact additive-flow
shift identity. -/
theorem concreteCenteredRankOneCOEEventPath_add
    {N : ℕ} (K : ℕ) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y t : ℝ) :
    concreteCenteredRankOneCOEEventPath K v event (y + t) =
      concreteCenteredRankOneCOEEventPath K v
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) y ⁻¹' event) t := by
  let Q := concreteCenteredOrbitalDirection N v
  have hflow (s : ℝ) : Measurable (transposeCongruenceFlow Q s) := by
    unfold transposeCongruenceFlow
    exact measurable_transposeCongruence _
  unfold concreteCenteredRankOneCOEEventPath
  rw [map_measureReal_apply (hflow (y + t)) hevent,
    map_measureReal_apply (hflow t) ((hflow y) hevent)]
  congr 1
  ext A
  simp only [Set.mem_preimage]
  rw [transposeCongruenceFlow_add]

/-- Every fixed-direction iterated derivative at time `y` is the
corresponding origin derivative for the shifted measurable event. -/
theorem iteratedDeriv_concreteCenteredRankOneCOEEventPath_eq_zero_shift
    {N : ℕ} (r K : ℕ) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) y =
      iteratedDeriv r
        (concreteCenteredRankOneCOEEventPath K v
          (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) y ⁻¹' event)) 0 := by
  let F := concreteCenteredRankOneCOEEventPath K v event
  let shiftedEvent := transposeCongruenceFlow
    (concreteCenteredOrbitalDirection N v) y ⁻¹' event
  have hfun : (fun t ↦ F (y + t)) =
      concreteCenteredRankOneCOEEventPath K v shiftedEvent := by
    funext t
    exact concreteCenteredRankOneCOEEventPath_add K v event hevent y t
  have hshift := congrFun (iteratedDeriv_comp_const_add r F y) 0
  rw [hfun] at hshift
  simpa only [add_zero, F, shiftedEvent] using hshift.symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
