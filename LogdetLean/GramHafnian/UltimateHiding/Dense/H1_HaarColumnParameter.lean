import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_OneColumnParameter
import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_HaarLastColumnUniform

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense
noncomputable section

def h1SphereDimCast {a b : ℕ} (h : a = b) :
    ComplexUnitSphere a ≃ᵐ ComplexUnitSphere b := by
  subst b
  exact MeasurableEquiv.refl _

theorem map_h1SphereDimCast_uniform {a b : ℕ} (h : a = b) :
    Measure.map (h1SphereDimCast h)
        (complexUnitSphereProbabilityMeasure a) =
      complexUnitSphereProbabilityMeasure b := by
  subst b
  change Measure.map id (complexUnitSphereProbabilityMeasure a) = _
  rw [Measure.map_id]

def h1HaarColumnParameter {N m : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (z : ComplexUnitSphere (m + 1)) : ℝ × ComplexUnitSphere N :=
  h1AmbientSphereParameter (r := m + 1 - N) hN
    (h1SphereDimCast
      (Nat.add_sub_of_le (hNm.trans (Nat.le_succ m))).symm z)

theorem measurable_h1HaarColumnParameter {N m : ℕ}
    (hN : 1 ≤ N) (hNm : N ≤ m) :
    Measurable (h1HaarColumnParameter hN hNm) := by
  unfold h1HaarColumnParameter
  exact (measurable_h1AmbientSphereParameter
    (N := N) (r := m + 1 - N) hN).comp
      (h1SphereDimCast _).measurable

theorem map_h1HaarColumnParameter_uniform {N m : ℕ}
    (hN : 1 ≤ N) (hNm : N ≤ m) :
    Measure.map (h1HaarColumnParameter hN hNm)
        (complexUnitSphereProbabilityMeasure (m + 1)) =
      concreteOneColumnParameterLaw m N := by
  have hr : 1 ≤ m + 1 - N := by omega
  have hbase := map_h1AmbientSphereParameter_uniform
    (N := N) (r := m + 1 - N) hN hr
  unfold concreteOneColumnParameterLaw oneColumnParameterLaw
    oneColumnBetaLaw oneColumnBetaShapeLeft oneColumnBetaShapeRight
  have hbase' :
      Measure.map (h1HaarColumnParameter hN hNm)
          (complexUnitSphereProbabilityMeasure (m + 1)) =
        (betaMeasure (m + 1 - N : ℕ) (N : ℝ)).prod
          (complexUnitSphereProbabilityMeasure N) := by
    rw [show h1HaarColumnParameter hN hNm =
        h1AmbientSphereParameter (r := m + 1 - N) hN ∘
          h1SphereDimCast
            (Nat.add_sub_of_le
              (hNm.trans (Nat.le_succ m))).symm by rfl]
    rw [← Measure.map_map
      (measurable_h1AmbientSphereParameter
        (N := N) (r := m + 1 - N) hN)
      (h1SphereDimCast _).measurable,
      map_h1SphereDimCast_uniform]
    exact hbase
  rw [hbase']
  congr 2
  rw [Nat.cast_sub (hNm.trans (Nat.le_succ m))]
  push_cast
  ring

theorem map_h1HaarColumnParameter_haarLastColumn {N m : ℕ}
    (hN : 1 ≤ N) (hNm : N ≤ m) :
    Measure.map (h1HaarColumnParameter hN hNm ∘
        haarLastColumnSphere (Nat.succ_le_succ (Nat.zero_le m)))
        (LogdetLean.GramHafnian.LocalAnticoncentration.unitaryHaarProbabilityMeasure (m + 1)) =
      concreteOneColumnParameterLaw m N := by
  rw [← Measure.map_map (measurable_h1HaarColumnParameter hN hNm)
    (measurable_haarLastColumnSphere (Nat.succ_le_succ (Nat.zero_le m))),
    map_haarLastColumnSphere_unitaryHaarProbabilityMeasure,
    map_h1HaarColumnParameter_uniform hN hNm]

end
end LogdetLean.GramHafnian.UltimateHiding.Dense
